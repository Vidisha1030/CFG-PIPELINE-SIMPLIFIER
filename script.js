const EXAMPLES={
basic:`S -> A B | a
A -> a A | ε
B -> b | C
C -> c | ε
D -> d`,
units:`S -> A
A -> B | a
B -> C | b
C -> c`,
useless:`S -> A | b
A -> a
B -> c
C -> D
D -> D`
};

let lastRun=null, history=JSON.parse(localStorage.getItem("cfgHistory")||"[]");

function parseCFG(text){
  const map=new Map(), lines=text.split(/\r?\n/);
  for(const raw of lines){
    const line=raw.trim(); if(!line||line.startsWith("#")) continue;
    const m=line.match(/^(.+?)\s*(?:→|->)\s*(.+)$/);
    if(!m) continue;
    const lhs=m[1].trim(); if(!/^[A-Z][A-Za-z0-9_]*$/.test(lhs)) throw new Error("Invalid variable: "+lhs);
    if(!map.has(lhs)) map.set(lhs,[]);
    for(const alt of m[2].split("|")){
      const a=alt.trim(); if(!a) continue;
      const normalized=a.replace(/\\bepsilon\\b/gi,"ε").replace(/^eps$/i,"ε");
      const symbols=normalized==="ε" ? ["ε"] : normalized.split(/\s+/).filter(Boolean);
      map.get(lhs).push(symbols);
    }
  }
  if(!map.size) throw new Error("No valid productions found.");
  return {start:[...map.keys()][0], map};
}
function cloneG(g){return {start:g.start,map:new Map([...g.map].map(([k,v])=>[k,v.map(x=>[...x])]))}}
function vars(g){return new Set(g.map.keys())}
function key(a){return a.join(" ")}
function ruleCount(g){let n=0;g.map.forEach(v=>n+=v.length);return n}
function grammarText(g){
  return [...g.map].map(([A,alts])=>`${A} → ${alts.map(a=>a.join(" ")||"ε").join(" | ")}`).join("\n");
}
function dedupe(g){
  for(const [A,alts] of g.map){
    const seen=new Set(), out=[];
    for(const a of alts){const k=key(a);if(!seen.has(k)){seen.add(k);out.push(a)}}
    g.map.set(A,out);
  }
  return g;
}
function generatingInfo(g){
  const V=vars(g), gen=new Set();
  let changed=true;
  while(changed){changed=false;
    for(const [A,alts] of g.map) for(const a of alts){
      if(a.length===1&&a[0]==="ε"){if(!gen.has(A)){gen.add(A);changed=true}}
      else if(a.every(s=>!V.has(s)||gen.has(s))){if(!gen.has(A)){gen.add(A);changed=true}}
    }
  }
  return gen;
}
function reachableInfo(g){
  const V=vars(g), reach=new Set([g.start]); let changed=true;
  while(changed){changed=false;
    for(const A of [...reach]){
      for(const a of g.map.get(A)||[]) for(const s of a){
        if(V.has(s)&&!reach.has(s)){reach.add(s);changed=true}
      }
    }
  }
  return reach;
}
function useless(g){
  const gen=generatingInfo(g), h={start:g.start,map:new Map()};
  for(const [A,alts] of g.map) if(gen.has(A)){
    const kept=alts.filter(a=>a.every(s=>s==="ε"||!vars(g).has(s)||gen.has(s)));
    if(kept.length) h.map.set(A,kept);
  }
  const reach=reachableInfo(h);
  for(const A of [...h.map.keys()]) if(!reach.has(A)) h.map.delete(A);
  for(const [A,alts] of h.map) h.map.set(A,alts.filter(a=>a.every(s=>s==="ε"||!vars(h).has(s)||reach.has(s))));
  return {grammar:dedupe(h),gen,reach};
}
function nullable(g){
  const V=vars(g), n=new Set(); let changed=true;
  while(changed){changed=false;
    for(const [A,alts] of g.map) for(const a of alts){
      if(a.length===1&&a[0]==="ε" || a.length&&a.every(s=>V.has(s)&&n.has(s))){
        if(!n.has(A)){n.add(A);changed=true}
      }
    }
  }
  return n;
}
function epsilonElim(g){
  const V = vars(g);
  const n = nullable(g);

  const out = {
    start: g.start,
    map: new Map()
  };

  for(const [A, alts] of g.map){

    const generated = new Map();

    for(const a of alts){

      // Completely remove original epsilon productions
      if(a.length === 1 && a[0] === "ε"){
        continue;
      }

      // Find nullable variables inside this production
      const positions = [];

      for(let i = 0; i < a.length; i++){
        const symbol = a[i];

        if(V.has(symbol) && n.has(symbol)){
          positions.push(i);
        }
      }

      // Generate every possible combination
      const combinations = 1 << positions.length;

      for(let mask = 0; mask < combinations; mask++){

        const remove = new Set();

        positions.forEach((position, index) => {
          if(mask & (1 << index)){
            remove.add(position);
          }
        });

        const newProduction = a.filter(
          (_, index) => !remove.has(index)
        );

        // IMPORTANT:
        // Never add ε back into the grammar.
        if(newProduction.length === 0){
          continue;
        }

        const productionKey = key(newProduction);

        generated.set(
          productionKey,
          newProduction
        );
      }
    }

    out.map.set(
      A,
      [...generated.values()]
    );
  }

  return {
    grammar: dedupe(out),
    nullable: n
  };
}
function unitElim(g){
  const V=vars(g), out={start:g.start,map:new Map()};
  for(const A of V){
    const closure=new Set([A]), q=[A];
    while(q.length){const X=q.shift();
      for(const a of g.map.get(X)||[]) if(a.length===1&&V.has(a[0])&&!closure.has(a[0])){closure.add(a[0]);q.push(a[0])}
    }
    const list=new Map();
    for(const X of closure) for(const a of g.map.get(X)||[]){
      if(!(a.length===1&&V.has(a[0]))) list.set(key(a),a);
    }
    out.map.set(A,[...list.values()]);
  }
  return dedupe(out);
}
function validate(g){
  const V=vars(g), n=nullable(g), gen=generatingInfo(g), reach=reachableInfo(g);
  let eps=0, unit=0;
  for(const [A,alts] of g.map) for(const a of alts){
    if(a.length===1&&a[0]==="ε")eps++;
    if(a.length===1&&V.has(a[0]))unit++;
  }
  return {eps,unit,vars:V.size,rules:ruleCount(g),nullable:n,gen,reach};
}
function runPipeline(){
  try{
    const raw=parseCFG(document.getElementById("grammarInput").value);
    const u=useless(raw), e=epsilonElim(u.grammar), un=unitElim(e.grammar);
    const final=un, vi=validate(final), rawInfo=validate(raw);
    lastRun={raw,u,e,un,final,rawInfo,vi,time:new Date().toLocaleString()};
    render(lastRun); saveHistory(lastRun);
    document.getElementById("statusText").textContent=`Completed in ${new Date().toLocaleTimeString()} — ${vi.vars} variables, ${vi.rules} rules.`;
  }catch(err){alert(err.message)}
}
function render(r){
  document.getElementById("finalGrammar").textContent=grammarText(r.final);
  document.getElementById("verification").textContent=r.vi.eps===0&&r.vi.unit===0?"✓ Verified":"⚠ Check grammar";
  document.getElementById("stats").innerHTML=[
    ["Variables",`${r.rawInfo.vars} → ${r.vi.vars}`],
    ["Productions",`${r.rawInfo.rules} → ${r.vi.rules}`],
    ["Epsilon Rules",`${r.rawInfo.eps} → ${r.vi.eps}`],
    ["Unit Rules",`${r.rawInfo.unit} → ${r.vi.unit}`]
  ].map(x=>`<div><span>${x[0]}</span><b>${x[1]}</b></div>`).join("");
  document.getElementById("uselessBefore").textContent=grammarText(r.raw);
  document.getElementById("uselessAfter").textContent=grammarText(r.u.grammar);
  document.getElementById("epsilonBefore").textContent=grammarText(r.u.grammar);
  document.getElementById("epsilonAfter").textContent=grammarText(r.e.grammar);
  document.getElementById("unitBefore").textContent=grammarText(r.e.grammar);
  document.getElementById("unitAfter").textContent=grammarText(r.final);
  document.getElementById("uselessBadge").textContent=`${r.rawInfo.vars-r.u.grammar.map.size} variables removed`;
  document.getElementById("epsilonBadge").textContent=`nullable: {${[...r.e.nullable].join(", ")}}`;
  document.getElementById("unitBadge").textContent=`${r.e.grammar.map.size} variables`;
  const rawV=vars(r.raw), tbody=[];
  for(const A of rawV){
    const g=r.u.gen.has(A), rr=r.u.reach.has(A), n=r.e.nullable.has(A);
    tbody.push(`<tr><td>${A}</td><td class="${g?"ok":"bad"}">${g?"✓":"✗"}</td><td class="${rr?"ok":"bad"}">${rr?"✓":"✗"}</td><td>${n?"yes":"no"}</td><td class="${r.final.map.has(A)?"ok":"bad"}">${r.final.map.has(A)?"Kept":"Removed"}</td></tr>`);
  }
  document.getElementById("symbolTable").innerHTML=tbody.join("");
  const log=[
    `parsed: ${r.rawInfo.vars} variables, ${r.rawInfo.rules} rules`,
    `step 1 — useless elimination`,
    `generating variables: ${[...r.u.gen].join(", ")||"none"}`,
    `after step 1: ${r.u.grammar.map.size} variables, ${ruleCount(r.u.grammar)} rules`,
    `step 2 — epsilon elimination`,
    `nullable variables: ${[...r.e.nullable].join(", ")||"none"}`,
    `after step 2: ${r.e.grammar.map.size} variables, ${ruleCount(r.e.grammar)} rules`,
    `step 3 — unit elimination`,
    `final: ${r.vi.vars} variables, ${r.vi.rules} rules`,
    `verification: epsilon=${r.vi.eps}, unit=${r.vi.unit}`
  ];
  document.getElementById("runLog").textContent=log.map((x,i)=>`[00.${String(i+1).padStart(2,"0")}] ${x}`).join("\n");
  document.querySelectorAll(".pipeline-step").forEach((el,i)=>el.classList.toggle("done",i<5));
}
function saveHistory(r){
  history.unshift({time:r.time,vars:r.vi.vars,rules:r.vi.rules,grammar:grammarText(r.final)});
  history=history.slice(0,10);localStorage.setItem("cfgHistory",JSON.stringify(history));renderHistory();
}
function renderHistory(){
  document.getElementById("historyList").innerHTML=history.length?history.map((h,i)=>`<div class="history-item"><b>Run ${history.length-i}</b> — ${h.time}<br><small>${h.vars} variables · ${h.rules} rules</small><pre>${h.grammar}</pre></div>`).join(""):"No completed runs yet.";
}
function showSection(id){
  document.querySelectorAll(".section").forEach(s=>s.classList.remove("active-section"));
  document.getElementById(id).classList.add("active-section");
  document.querySelectorAll(".nav-item").forEach(n=>n.classList.toggle("active",n.dataset.section===id));
}
function download(name,text,type="text/plain"){
  const a=document.createElement("a");a.href=URL.createObjectURL(new Blob([text],{type}));a.download=name;a.click();URL.revokeObjectURL(a.href);
}
document.getElementById("runBtn").onclick=runPipeline;
document.getElementById("runBtn2").onclick=runPipeline;
document.getElementById("exampleBtn").onclick=()=>document.getElementById("grammarInput").value=EXAMPLES.basic;
document.getElementById("examplesBtn").onclick=()=>showSection("examples");
document.getElementById("clearBtn").onclick=()=>document.getElementById("grammarInput").value="";
document.getElementById("copyBtn").onclick=async()=>{if(lastRun)await navigator.clipboard.writeText(grammarText(lastRun.final));};
document.getElementById("txtBtn").onclick=()=>{if(lastRun)download("cfg-final.txt",grammarText(lastRun.final))};
document.getElementById("jsonBtn").onclick=()=>{if(lastRun)download("cfg-result.json",JSON.stringify({input:document.getElementById("grammarInput").value,final:grammarText(lastRun.final)},null,2),"application/json")};
document.getElementById("reportBtn").onclick=()=>{if(lastRun)download("cfg-report.txt",`CFG SIMPLIFIER REPORT\n\n${grammarText(lastRun.final)}\n\nVerified: epsilon=${lastRun.vi.eps}, unit=${lastRun.vi.unit}`)};
document.getElementById("downloadNav").onclick=()=>document.getElementById("txtBtn").click();
document.getElementById("clearLogBtn").onclick=()=>document.getElementById("runLog").textContent="No run yet.";
document.getElementById("themeBtn").onclick=()=>{document.body.classList.toggle("dark");document.getElementById("themeBtn").textContent=document.body.classList.contains("dark")?"☀ Light mode":"◐ Dark mode"};
document.querySelectorAll(".nav-item").forEach(n=>n.onclick=()=>showSection(n.dataset.section));
document.querySelectorAll(".example-choice").forEach(b=>b.onclick=()=>{document.getElementById("grammarInput").value=EXAMPLES[b.dataset.example];showSection("pipeline");runPipeline()});
document.getElementById("fileInput").onchange=e=>{const f=e.target.files[0];if(f){const r=new FileReader();r.onload=()=>document.getElementById("grammarInput").value=r.result;r.readAsText(f)}};
renderHistory();
