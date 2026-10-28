const bitCount = n => n.toString(2).replace(/0/g, '').length;
    const monoDegree = m => 2*m[0] + bitCount(m[1]);
    const monomialKey = m => m[0] + ':' + m[1];
    const vectorKey = (d,a,mask) => d + ':' + a + ':' + mask;
    const basisCache = new Map();
    const inverseCache = new Map();
    function basis(n) {
      if (basisCache.has(n)) return basisCache.get(n);
      let out = [];
      if (n === 0) out = [[0,0]];
      else if (n === 1) out = [[0,0],[0,1],[0,2],[0,4],[0,8],[1,0]];
      else if (n === 2) {
        out = [[0,0],[0,1],[0,2],[0,4],[0,8],[1,0]];
        for (let i=1;i<16;i++) if (bitCount(i) === 2) out.push([0,i]);
        out.push([1,1],[1,2],[1,4],[1,8],[2,0]);
      } else {
        for (let a=0;a<=n-2;a++) for (let i=0;i<16;i++) out.push([a,i]);
      }
      out.sort((x,y) => monoDegree(x)-monoDegree(y) || x[0]-y[0] || x[1]-y[1]);
      basisCache.set(n,out);
      return out;
    }
    function wedge(i,j) {
      if (i & j) return [0,0];
      let inversions = 0;
      for (let k=0;k<4;k++) if (i & (1<<k)) inversions += bitCount(j & ((1<<k)-1));
      return [inversions%2 ? -1 : 1,i|j];
    }
    function addTerm(v,k,c) {
      const value = (v.get(k)||0) + c;
      if (!Number.isSafeInteger(value)) throw new Error('Integer range exceeded');
      if (value) v.set(k,value); else v.delete(k);
    }
    function add(v,w,scale) {
      const out = new Map(v);
      for (const [k,c] of w) addTerm(out,k,c*scale);
      return out;
    }
    function reduceMono(n,a,mask) {
      const out = new Map();
      const degree = 2*a + bitCount(mask);
      if (degree > 2*n) return out;
      if (n === 0) { if (!degree) out.set('0:0',1); return out; }
      if (n === 1) {
        if (degree < 2) out.set(a+':'+mask,1);
        else if ((a===1 && mask===0) || mask===3 || mask===12) out.set('1:0',1);
        return out;
      }
      if (n === 2) {
        if (degree<=2 || (degree===3 && a===1)) out.set(a+':'+mask,1);
        else if (degree===3) out.set('1:'+((mask & 3) === 3 ? mask ^ 3 : mask ^ 12),1);
        else if (degree===4 && ((a===2 && mask===0) || (a===1 && (mask===3 || mask===12)) || mask===15)) out.set('2:0',1);
        return out;
      }
      if (a<=n-2) { out.set(a+':'+mask,1); return out; }
      for (const [pairMask,shift,c] of [[3,1,1],[12,1,1],[15,2,-1]]) {
        const [s,j] = wedge(pairMask,mask);
        if (!s) continue;
        for (const [k,v] of reduceMono(n,a-shift,j)) addTerm(out,k,c*s*v);
      }
      return out;
    }
    function integral(n,a,mask) {
      if (2*a+bitCount(mask)!==2*n) return 0;
      return reduceMono(n,a,mask).get(n<=2 ? n+':0' : (n-2)+':15') || 0;
    }
    function gram(n,x,y) {
      const [s,j] = wedge(x[1],y[1]);
      return s ? s*integral(n,x[0]+y[0],j) : 0;
    }
    function gramInverse(n) {
      if (inverseCache.has(n)) return inverseCache.get(n);
      const B=basis(n), G=B.map(x=>B.map(y=>gram(n,x,y))), size=B.length;
      const a=G.map((r,i)=>r.concat(B.map((_,j)=>i===j ? 1 : 0)));
      for (let col=0;col<size;col++) {
        const pivot=a.findIndex((r,i)=>i>=col && r[col]!==0);
        if (pivot<0) throw new Error('Singular Gram matrix');
        [a[col],a[pivot]]=[a[pivot],a[col]];
        const v=a[col][col];
        for (let j=0;j<2*size;j++) a[col][j]/=v;
        for (let i=0;i<size;i++) if(i!==col) {
          const c=a[i][col];
          for (let j=0;j<2*size;j++) a[i][j]-=c*a[col][j];
        }
      }
      const inv=a.map(r=>r.slice(size).map(Math.round));
      for(let i=0;i<size;i++) for(let j=0;j<size;j++) {
        const v=G[i].reduce((sum,c,k)=>sum+c*inv[k][j],0);
        if(v!==(i===j?1:0)) throw new Error('Inverse failed exact integer identity');
      }
      inverseCache.set(n,inv); return inv;
    }
    function index(b,g,d,m) {
      return (d-m+1)*(d+m)*b-2*(d-m)+2*g*(d-m+1);
    }
    function pairing(b,g,m,d,x,y,point) {
      if(m>d) return 0;
      const [s,mask]=wedge(x[1],y[1]);
      if(!s || 2*(x[0]+y[0]+(point?1:0))+bitCount(mask)!==index(b,g,d,m)) return 0;
      if(![0,3,12,15].includes(mask)) return 0;
      return s*Math.pow(d-m+1,2-bitCount(mask)/2);
    }
    function rawU(b,g,v) {
      const out=new Map();
      for(const [k,c] of v) {
        const [d,a,mask]=k.split(':').map(Number), n=b*d+g;
        for(const [target,value] of reduceMono(n,a+1,mask)) {
          const [aa,mm]=target.split(':').map(Number);
          addTerm(out,vectorKey(d,aa,mm),c*value);
        }
        if(d>0 && a===n-2) for(const [target,value] of reduceMono(b*(d-1)+g,0,mask)) {
          const [aa,mm]=target.split(':').map(Number);
          addTerm(out,vectorKey(d-1,aa,mm),c*value);
        }
      }
      return out;
    }
    function R(b,g,v) {
      const low=basis(g), inv=gramInverse(g), rhs=low.map(()=>0);
      for(const [k,c] of v) {
        const [d,a,mask]=k.split(':').map(Number);
        if(d!==1) continue;
        low.forEach((x,i)=>rhs[i]+=c*pairing(b,g,0,1,x,[a,mask],false));
      }
      const out=new Map();
      inv.forEach((row,i)=>{
        const value=row.reduce((sum,c,j)=>sum+c*rhs[j],0);
        if(value) addTerm(out,vectorKey(0,low[i][0],low[i][1]),value);
      });
      return out;
    }
    function unit(d,a,mask) { return new Map([[vectorKey(d,a,mask),1]]); }
    function computeU(b,g,source,mode) {
      const input=unit(source[0],source[1],source[2]);
      if(mode==='raw') return rawU(b,g,input);
      if(mode==='corrected') {
        const result=rawU(b,g,add(input,R(b,g,input),-1));
        return add(result,R(b,g,result),1);
      }
      const result=rawU(b,g,input);
      return add(result,R(b,g,result),1);
    }
    function evaluateP(b,g,m,x,v,corrected) {
      let total=0;
      for(const [key,c] of v) {
        const [d,a,mask]=key.split(':').map(Number);
        total+=c*(corrected ? (m===d ? gram(b*m+g,x,[a,mask]):0) : pairing(b,g,m,d,x,[a,mask],false));
      }
      return total;
    }
    function residual(b,g,D,source,mode,v) {
      let failures=0, witness=null;
      let input=unit(source[0],source[1],source[2]);
      if(mode==='corrected') input=add(input,R(b,g,input),-1);
      for(let m=0;m<=D;m++) for(const x of basis(b*m+g)) {
        const actual=evaluateP(b,g,m,x,v,mode==='corrected');
        let expected=0;
        for(const [key,c] of input) {
          const [d,a,mask]=key.split(':').map(Number);
          expected+=c*pairing(b,g,m,d,x,[a,mask],true);
        }
        if(actual!==expected) {
          failures++;
          if(!witness) witness={m,x,actual,expected};
        }
      }
      return {failures,witness};
    }
    function entries(b,g) {
      const out=[];
      for(const x of basis(g)) for(const y of basis(b+g)) {
        const value=pairing(b,g,0,1,x,y,false);
        if(value) out.push({x,y,value});
      }
      return out;
    }
    function serialize(v) {
      return Array.from(v,([k,c])=>k.split(':').map(Number).concat(c)).sort((a,b)=>a[0]-b[0]||a[1]-b[1]||a[2]-b[2]);
    }
    function weight(b,g,source) {
      const [d,a,mask]=source;
      return b*d*(d+1)+2*d*(g-1)+2*g-2*a-bitCount(mask);
    }
    function traceU(b,g,source,mode,steps) {
      const out=[unit(...source)];
      for(let i=0;i<steps;i++) {
        const next=new Map();
        for(const [key,c] of out[i]) {
          const src=key.split(':').map(Number);
          for(const [target,k] of computeU(b,g,src,mode)) addTerm(next,target,c*k);
        }
        out.push(next);
      }
      return out;
    }
    