/* Fresh-numbers question generators. Each make(rng) returns {q, o:[correct, d1, d2, d3], w}.
   rng is a seeded PRNG returning [0,1). Pure functions: same seed -> same question. */
(function (root) {
  'use strict';
  function mulberry32(a) { return function () { a |= 0; a = a + 0x6D2B79F5 | 0; var t = Math.imul(a ^ a >>> 15, 1 | a); t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t; return ((t ^ t >>> 14) >>> 0) / 4294967296; }; }
  var R = function (rng) {
    return {
      int: function (a, b) { return a + Math.floor(rng() * (b - a + 1)); },
      pick: function (arr) { return arr[Math.floor(rng() * arr.length)]; },
      shuffle: function (arr) { arr = arr.slice(); for (var i = arr.length - 1; i > 0; i--) { var j = Math.floor(rng() * (i + 1)); var t = arr[i]; arr[i] = arr[j]; arr[j] = t; } return arr; },
      sample: function (arr, k) { return this.shuffle(arr).slice(0, k); }
    };
  };
  function fmt(x) { if (typeof x !== 'number') return String(x); var r = Math.round(x * 100) / 100; return String(r); }
  // Build 4 distinct options: correct first, then candidates, then perturbations of correct.
  function opts(correct, cands, perturb) {
    var c = fmt(correct), out = [c], seen = {}; seen[c] = 1;
    (cands || []).forEach(function (v) { var s = fmt(v); if (out.length < 4 && !seen[s]) { seen[s] = 1; out.push(s); } });
    var k = 1, guard = 0;
    while (out.length < 4 && guard++ < 200) {
      var v = perturb ? perturb(k) : (typeof correct === 'number' ? correct + (k % 2 ? 1 : -1) * Math.ceil(k / 2) * (Math.abs(correct) >= 10 ? Math.max(1, Math.round(Math.abs(correct) * 0.1)) : 1) : null);
      k++;
      if (v === null || v === undefined) break;
      var s = fmt(v); if (!seen[s] && !(typeof v === 'number' && v < 0 && correct >= 0)) { seen[s] = 1; out.push(s); }
    }
    return out;
  }

  /* ---------- OS helpers ---------- */
  function names(n) { var a = []; for (var i = 1; i <= n; i++) a.push('P' + i); return a; }
  function procTable(P, withPri) { return P.map(function (p) { return p.n + '(AT ' + p.a + ', BT ' + p.b + (withPri ? ', Pri ' + p.p : '') + ')'; }).join(', '); }
  function sched(P, algo, q) {
    var t = 0, done = {}, rem = {}, order = [], i;
    P.forEach(function (p) { rem[p.n] = p.b; });
    var byArr = P.slice().sort(function (x, y) { return x.a - y.a || x.idx - y.idx; });
    if (algo === 'fcfs') { byArr.forEach(function (p) { t = Math.max(t, p.a); t += p.b; done[p.n] = t; }); }
    else if (algo === 'sjf' || algo === 'prio') {
      var left = byArr.slice();
      while (left.length) {
        var av = left.filter(function (p) { return p.a <= t; });
        if (!av.length) { t = Math.min.apply(null, left.map(function (p) { return p.a; })); continue; }
        av.sort(function (x, y) { return (algo === 'sjf' ? x.b - y.b : x.p - y.p) || x.a - y.a || x.idx - y.idx; });
        var c = av[0]; t += c.b; done[c.n] = t; left.splice(left.indexOf(c), 1);
      }
    } else if (algo === 'srtf') {
      var cnt = 0;
      while (cnt < P.length) {
        var av2 = byArr.filter(function (p) { return p.a <= t && rem[p.n] > 0; });
        if (!av2.length) { t++; continue; }
        av2.sort(function (x, y) { return rem[x.n] - rem[y.n] || x.a - y.a || x.idx - y.idx; });
        var c2 = av2[0]; rem[c2.n]--; t++; if (rem[c2.n] === 0) { done[c2.n] = t; cnt++; }
      }
    } else if (algo === 'rr') {
      var Q = [], ii = 0, fin = 0;
      while (fin < P.length) {
        while (ii < byArr.length && byArr[ii].a <= t) Q.push(byArr[ii++]);
        if (!Q.length) { t = byArr[ii].a; continue; }
        var c3 = Q.shift(), run = Math.min(q, rem[c3.n]); t += run; rem[c3.n] -= run;
        while (ii < byArr.length && byArr[ii].a <= t) Q.push(byArr[ii++]);
        if (rem[c3.n] === 0) { done[c3.n] = t; fin++; } else Q.push(c3);
      }
    }
    var tat = 0, wt = 0;
    P.forEach(function (p) { tat += done[p.n] - p.a; wt += done[p.n] - p.a - p.b; });
    return { ct: done, tat: tat / P.length, wt: wt / P.length };
  }
  function genProcs(r, n, maxA, maxB, pri) {
    var P = [], a = 0;
    for (var i = 0; i < n; i++) { P.push({ n: 'P' + (i + 1), idx: i, a: i === 0 ? 0 : (a += r.int(0, maxA)), b: r.int(1, maxB), p: pri ? r.int(1, 6) : 0 }); }
    return P;
  }
  function pr(ref, f, algo) {
    var m = [], faults = 0;
    ref.forEach(function (p, i) {
      var hit = m.indexOf(p) >= 0;
      if (algo === 'lru') { if (hit) { m.splice(m.indexOf(p), 1); m.push(p); return; } faults++; if (m.length === f) m.shift(); m.push(p); return; }
      if (hit) return; faults++;
      if (m.length < f) { m.push(p); return; }
      if (algo === 'fifo') { m.shift(); m.push(p); return; }
      var fut = ref.slice(i + 1), best = -1, vi = 0;
      m.forEach(function (x, j) { var d = fut.indexOf(x); d = d < 0 ? 1e9 : d; if (d > best) { best = d; vi = j; } });
      m[vi] = p;
    });
    return faults;
  }
  function disk(req, h, algo, dir, maxC) {
    var s = 0, c = h, order = [];
    function go(x) { s += Math.abs(x - c); c = x; order.push(x); }
    var lo = req.filter(function (x) { return x < h; }).sort(function (a, b) { return b - a; });
    var hi = req.filter(function (x) { return x >= h; }).sort(function (a, b) { return a - b; });
    if (algo === 'fcfs') req.forEach(go);
    else if (algo === 'sstf') { var left = req.slice(); while (left.length) { left.sort(function (a, b) { return Math.abs(a - c) - Math.abs(b - c) || a - b; }); go(left.shift()); } }
    else if (algo === 'scan' || algo === 'look') {
      var first = dir === 'up' ? hi : lo, second = dir === 'up' ? lo : hi;
      first.forEach(go);
      if (second.length) { if (algo === 'scan') go(dir === 'up' ? maxC : 0); second.forEach(go); }
    } else if (algo === 'cscan' || algo === 'clook') {
      // direction up only (standard)
      hi.forEach(go);
      var lowAsc = lo.slice().sort(function (a, b) { return a - b; });
      if (lowAsc.length) { if (algo === 'cscan') { go(maxC); go(0); } else { go(lowAsc[0]); lowAsc.shift(); } lowAsc.forEach(go); }
    }
    return { total: s, order: order };
  }

  var G = {};

  /* ===================== OS ===================== */
  function schedGen(algo, label, metric) {
    return function (rng) {
      var r = R(rng), n = r.int(4, 5), q = r.int(2, 3), pri = algo === 'prio';
      var P = genProcs(r, n, 3, 8, pri);
      var res = sched(P, algo, q), other = ['fcfs', 'sjf', 'srtf', 'rr'].filter(function (x) { return x !== algo; });
      var cands = other.map(function (a) { return sched(P, a, q)[metric]; });
      cands.push(metric === 'wt' ? res.tat : res.wt);
      var o = opts(res[metric], cands, function (k) { return res[metric] + (k % 2 ? 0.5 : -0.5) * Math.ceil(k / 2); });
      var mname = metric === 'wt' ? 'average waiting time' : 'average turnaround time';
      return {
        q: 'Using ' + label + (algo === 'rr' ? ' (time quantum = ' + q + ')' : '') + (pri ? ' (lower number = higher priority)' : '') + ', find the ' + mname + ' for: ' + procTable(P, pri) + '.',
        o: o,
        w: 'Completion times: ' + P.map(function (p) { return p.n + '=' + res.ct[p.n]; }).join(', ') + '. TAT = CT − AT, WT = TAT − BT. Average TAT = ' + fmt(res.tat) + ', average WT = ' + fmt(res.wt) + '. Ties are broken by arrival order.'
      };
    };
  }
  G['os.fcfs'] = { s: 'OS', t: 'CPU scheduling', make: schedGen('fcfs', 'FCFS', 'wt') };
  G['os.sjf'] = { s: 'OS', t: 'CPU scheduling', make: schedGen('sjf', 'non-pre-emptive SJF', 'wt') };
  G['os.srtf'] = { s: 'OS', t: 'CPU scheduling', make: schedGen('srtf', 'SRTF (pre-emptive SJF)', 'wt') };
  G['os.rr'] = { s: 'OS', t: 'CPU scheduling', make: schedGen('rr', 'Round Robin', 'tat') };
  G['os.prio'] = { s: 'OS', t: 'CPU scheduling', make: schedGen('prio', 'non-pre-emptive priority scheduling', 'wt') };

  function refString(r) { var n = r.int(12, 16), pages = r.int(5, 7), a = []; for (var i = 0; i < n; i++) { var p; do { p = r.int(0, pages - 1); } while (a.length && a[a.length - 1] === p); a.push(p); } return a; }
  function prGen(algo, label) {
    return function (rng) {
      var r = R(rng), ref = refString(r), f = r.int(3, 4), ans = pr(ref, f, algo);
      var others = ['fifo', 'lru', 'opt'].filter(function (x) { return x !== algo; }).map(function (a) { return pr(ref, f, a); });
      others.push(pr(ref, f === 3 ? 4 : 3, algo));
      return { q: 'Page reference string: ' + ref.join(' ') + '. With ' + f + ' frames (initially empty), how many page faults occur under ' + label + '?', o: opts(ans, others), w: label + ' gives ' + ans + ' faults (FIFO ' + pr(ref, f, 'fifo') + ', LRU ' + pr(ref, f, 'lru') + ', Optimal ' + pr(ref, f, 'opt') + '). The first loads into empty frames count as faults.' };
    };
  }
  G['os.fifo'] = { s: 'OS', t: 'Page replacement', make: prGen('fifo', 'FIFO') };
  G['os.lru'] = { s: 'OS', t: 'Page replacement', make: prGen('lru', 'LRU') };
  G['os.opt'] = { s: 'OS', t: 'Page replacement', make: prGen('opt', 'Optimal') };

  function diskReq(r, maxC) { var n = r.int(6, 8), a = []; while (a.length < n) { var x = r.int(1, maxC - 1); if (a.indexOf(x) < 0) a.push(x); } return a; }
  function diskGen(algo, label) {
    return function (rng) {
      var r = R(rng), maxC = r.pick([199, 99]), req, h; do { req = diskReq(r, maxC); h = r.int(10, maxC - 10); } while (req.indexOf(h) >= 0 || !req.some(function (x) { return x < h; }) || !req.some(function (x) { return x > h; }));
      var dir = (algo === 'scan' || algo === 'look') ? r.pick(['up', 'down']) : 'up';
      var res = disk(req, h, algo, dir, maxC);
      var cands = ['fcfs', 'sstf', 'scan', 'look', 'cscan', 'clook'].filter(function (x) { return x !== algo; }).map(function (a) { return disk(req, h, a, dir, maxC).total; });
      var dirTxt = (algo === 'fcfs' || algo === 'sstf') ? '' : ' The head is moving towards ' + (dir === 'up' ? 'the higher cylinders (' + maxC + ')' : 'cylinder 0') + '.';
      var extra = algo === 'cscan' ? ' Count the return jump from ' + maxC + ' to 0 as head movement.' : (algo === 'clook' ? ' Count the jump back as head movement.' : '');
      return { q: 'A disk has cylinders 0–' + maxC + '. The head is at ' + h + '. Request queue: ' + req.join(', ') + '.' + dirTxt + extra + ' Total head movement under ' + label + '?', o: opts(res.total, cands), w: 'Order: ' + h + ' → ' + res.order.join(' → ') + '. Total = ' + res.total + ' cylinders.' };
    };
  }
  G['os.dfcfs'] = { s: 'OS', t: 'Disk scheduling', make: diskGen('fcfs', 'FCFS') };
  G['os.dsstf'] = { s: 'OS', t: 'Disk scheduling', make: diskGen('sstf', 'SSTF') };
  G['os.dscan'] = { s: 'OS', t: 'Disk scheduling', make: diskGen('scan', 'SCAN') };
  G['os.dlook'] = { s: 'OS', t: 'Disk scheduling', make: diskGen('look', 'LOOK') };
  G['os.dcscan'] = { s: 'OS', t: 'Disk scheduling', make: function (rng) { var r = R(rng); return diskGen(r.pick(['cscan', 'clook']), '')(rng); } };
  // fix label for C-variants
  G['os.dcscan'].make = function (rng) { var r = R(rng); var a = r.pick(['cscan', 'clook']); return diskGen(a, a === 'cscan' ? 'C-SCAN' : 'C-LOOK')(rng); };

  G['os.tlb'] = { s: 'OS', t: 'TLB', make: function (rng) {
    var r = R(rng), tlb = r.pick([10, 20, 5, 15]), mm = r.pick([100, 80, 120, 150, 200]), h = r.pick([80, 85, 90, 95, 70, 75]);
    var H = h / 100, ans = H * (tlb + mm) + (1 - H) * (tlb + 2 * mm);
    var c = [H * (tlb + mm) + (1 - H) * (tlb + mm), H * tlb + (1 - H) * (tlb + 2 * mm), H * (tlb + mm) + (1 - H) * (2 * mm), H * mm + (1 - H) * 2 * mm];
    return { q: 'TLB access time = ' + tlb + ' ns, main-memory access time = ' + mm + ' ns, TLB hit ratio = ' + h + '%. What is the effective memory access time (ns)?', o: opts(ans, c), w: 'EMAT = H(TLB + MM) + (1 − H)(TLB + 2·MM) = ' + H + '×' + (tlb + mm) + ' + ' + fmt(1 - H) + '×' + (tlb + 2 * mm) + ' = ' + fmt(ans) + ' ns.' };
  } };
  G['os.eat'] = { s: 'OS', t: 'Virtual memory', make: function (rng) {
    var r = R(rng), ma = r.pick([100, 200, 150]), pf = r.pick([8, 10, 5, 2]) /* ms */, pnum = r.pick([1, 2, 5, 4]), pden = r.pick([1000, 10000, 100000]);
    var p = pnum / pden, svc = pf * 1e6, ans = (1 - p) * ma + p * svc;
    var c = [p * svc, ma + svc * pnum / 1000, (1 - p) * ma + p * svc / 1000, ma + p * svc + ma];
    return { q: 'Memory access time = ' + ma + ' ns, page-fault service time = ' + pf + ' ms, page-fault rate p = ' + pnum + '/' + pden + '. Effective access time (ns)?', o: opts(ans, c), w: 'EAT = (1 − p)·ma + p·service = ' + fmt((1 - p) * ma) + ' + ' + fmt(p * svc) + ' = ' + fmt(ans) + ' ns (1 ms = 10⁶ ns).' };
  } };
  G['os.pbits'] = { s: 'OS', t: 'Paging', make: function (rng) {
    var r = R(rng), va = r.pick([32, 36, 40, 48, 30]), pa = r.pick([24, 28, 30, 32]), pk = r.pick([1, 2, 4, 8, 16]);
    var off = 10 + Math.log2(pk); if (pa <= off + 2) pa = off + 12;
    var vpn = va - off, pfn = pa - off;
    var ask = r.pick(['both', 'pt']);
    if (ask === 'both') return { q: 'A system has a ' + va + '-bit virtual address, a ' + pa + '-bit physical address and ' + pk + ' KB pages. Bits needed for the virtual page number and the physical frame number?', o: [vpn + ', ' + pfn, pfn + ', ' + vpn, (vpn - 1) + ', ' + (pfn - 1), va + ', ' + pa].filter(function (v, i, a) { return a.indexOf(v) === i; }).concat([(vpn + 1) + ', ' + (pfn + 1)]).slice(0, 4), w: 'Offset = log₂(' + pk + ' K) = ' + off + ' bits. VPN = ' + va + ' − ' + off + ' = ' + vpn + '; frame number = ' + pa + ' − ' + off + ' = ' + pfn + '.' };
    var entries = Math.pow(2, vpn), eb = r.pick([4, 2, 8]), size = vpn + Math.log2(eb);
    function pw(e) { return e >= 30 ? Math.pow(2, e - 30) + ' GB' : e >= 20 ? Math.pow(2, e - 20) + ' MB' : e >= 10 ? Math.pow(2, e - 10) + ' KB' : Math.pow(2, e) + ' B'; }
    return { q: 'Virtual address = ' + va + ' bits, page size = ' + pk + ' KB, page-table entry = ' + eb + ' bytes. Size of a single-level page table?', o: opts(pw(size), [pw(size - 1), pw(size + 1), pw(size + 2), pw(size - 2)]), w: 'Pages = 2^(' + va + '−' + off + ') = 2^' + vpn + '. Size = 2^' + vpn + ' × ' + eb + ' B = 2^' + size + ' B = ' + pw(size) + '.' };
  } };
  G['os.fork'] = { s: 'OS', t: 'fork', make: function (rng) {
    var r = R(rng), n = r.int(2, 6), ask = r.pick(['total', 'child', 'print']);
    var total = Math.pow(2, n);
    if (ask === 'total') return { q: 'A program calls fork() ' + n + ' times in sequence (no conditions). How many processes exist in total, including the original?', o: opts(total, [total - 1, 2 * n, n + 1]), w: 'Each fork doubles the processes: 2^' + n + ' = ' + total + ' (' + (total - 1) + ' new children).' };
    if (ask === 'child') return { q: 'A program calls fork() ' + n + ' times in sequence. How many NEW child processes are created?', o: opts(total - 1, [total, 2 * n, n]), w: '2^' + n + ' − 1 = ' + (total - 1) + '.' };
    return { q: 'main() { ' + Array(n + 1).join('fork(); ') + 'printf("hi\\n"); } — how many times is "hi" printed?', o: opts(total, [total - 1, n, 2 * n]), w: 'Every one of the 2^' + n + ' = ' + total + ' processes runs the printf.' };
  } };
  G['os.bank'] = { s: 'OS', t: "Banker's algorithm", make: function (rng) {
    var r = R(rng);
    for (var tries = 0; tries < 200; tries++) {
      var n = 4, m = 3, alloc = [], need = [], avail = [r.int(1, 3), r.int(1, 3), r.int(0, 2)];
      for (var i = 0; i < n; i++) { alloc.push([r.int(0, 3), r.int(0, 2), r.int(0, 3)]); need.push([r.int(0, 4), r.int(0, 3), r.int(0, 3)]); }
      // find all safe sequences via DFS in index order (standard: lowest index first)
      var work = avail.slice(), fin = [0, 0, 0, 0], seq = [];
      var progress = true;
      while (progress) { progress = false; for (var k = 0; k < n; k++) { if (!fin[k] && need[k].every(function (v, j) { return v <= work[j]; })) { work = work.map(function (w, j) { return w + alloc[k][j]; }); fin[k] = 1; seq.push(k); progress = true; break; } } }
      var safe = seq.length === n;
      if (!safe && r.int(0, 2) > 0) continue; // prefer safe instances
      var tbl = alloc.map(function (a, k) { return 'P' + k + ': Alloc ' + a.join(' ') + ', Need ' + need[k].join(' '); }).join('; ');
      var correct = safe ? 'Safe: ' + seq.map(function (k) { return 'P' + k; }).join(' → ') : 'Unsafe (no safe sequence)';
      var d = [];
      if (safe) { d.push('Unsafe (no safe sequence)'); var s2 = seq.slice().reverse(); d.push('Safe: ' + s2.map(function (k) { return 'P' + k; }).join(' → ')); d.push('Safe: P0 → P1 → P2 → P3'); d.push('Safe: P3 → P2 → P1 → P0'); d.push('Safe: P1 → P0 → P3 → P2'); }
      else { d = ['Safe: P0 → P1 → P2 → P3', 'Safe: P1 → P3 → P0 → P2', 'Safe: P2 → P0 → P1 → P3', 'Safe: P3 → P1 → P2 → P0']; }
      // remove distractors that are themselves valid safe sequences
      function valid(str) { if (str.indexOf('Safe:') !== 0) return !safe ? true : false; var ks = str.replace('Safe: ', '').split(' → ').map(function (x) { return +x.slice(1); }); var w = avail.slice(); for (var z = 0; z < ks.length; z++) { var kk = ks[z]; if (!need[kk].every(function (v, j) { return v <= w[j]; })) return false; w = w.map(function (x, j) { return x + alloc[kk][j]; }); } return true; }
      d = d.filter(function (s) { return s !== correct && !valid(s); });
      var o = [correct]; d.forEach(function (s) { if (o.length < 4 && o.indexOf(s) < 0) o.push(s); });
      if (o.length < 4) continue;
      return { q: "Banker's algorithm, 3 resource types. Available = " + avail.join(' ') + '. ' + tbl + '. Taking the lowest-numbered process that can run at each step, what is the result?', o: o, w: safe ? 'Run any process with Need ≤ Work, then Work += its Allocation. Sequence ' + correct.replace('Safe: ', '') + '. The other listed orders fail at some step.' : 'At some point no remaining process has Need ≤ Work, so the state is unsafe. Each listed order fails at some step.' };
    }
    return G['os.fork'].make(rng);
  } };
  G['os.disktime'] = { s: 'OS', t: 'Disk', make: function (rng) {
    var r = R(rng), rpm = r.pick([3000, 6000, 7200, 1500, 12000, 15000]), rot = 60000 / rpm, ask = r.pick(['lat', 'cap']);
    if (ask === 'lat') return { q: 'A disk spins at ' + rpm + ' RPM. What is its average rotational latency (ms)?', o: opts(rot / 2, [rot, rot / 4, rot * 2]), w: 'One rotation = 60,000 / ' + rpm + ' = ' + fmt(rot) + ' ms; average latency = half a rotation = ' + fmt(rot / 2) + ' ms.' };
    var tr = r.pick([256, 512, 1024]), sec = r.pick([64, 128, 256]), bs = r.pick([256, 512, 1024]), sur = r.pick([2, 4, 8]);
    var bytes = tr * sec * bs * sur; function sz(b) { return b >= 1 << 30 ? b / (1 << 30) + ' GB' : b >= 1 << 20 ? b / (1 << 20) + ' MB' : b / 1024 + ' KB'; }
    return { q: 'A disk has ' + sur + ' surfaces, ' + tr + ' tracks per surface, ' + sec + ' sectors per track and ' + bs + ' bytes per sector. Total capacity?', o: opts(sz(bytes), [sz(bytes / sur), sz(bytes * 2), sz(bytes / 2), sz(bytes * 4), sz(bytes / 4)]), w: sur + ' × ' + tr + ' × ' + sec + ' × ' + bs + ' B = ' + sz(bytes) + '.' };
  } };
  G['os.fit'] = { s: 'OS', t: 'Memory allocation', make: function (rng) {
    var r = R(rng), algo = r.pick(['first', 'best', 'worst']);
    for (var t = 0; t < 100; t++) {
      var parts = r.shuffle([100, 500, 200, 300, 600, 250, 400, 150]).slice(0, 5);
      var procs = [r.int(10, 45) * 10 + 2, r.int(10, 45) * 10 + 7, r.int(5, 30) * 10 + 2, r.int(20, 50) * 10 + 6];
      function run(a) { var holes = parts.slice(), res = []; procs.forEach(function (p) { var idx = -1; holes.forEach(function (h, i) { if (h >= p) { if (idx < 0) idx = i; else if (a === 'best' && h < holes[idx]) idx = i; else if (a === 'worst' && h > holes[idx]) idx = i; } }); if (a === 'first') { idx = holes.findIndex(function (h) { return h >= p; }); } if (idx < 0) res.push(p + ' K waits'); else { res.push(p + ' K → ' + holes[idx] + ' K hole'); holes[idx] -= p; } }); return res; }
      var res = run(algo), waits = res.filter(function (x) { return /waits/.test(x); }).map(function (x) { return x.split(' ')[0] + ' K'; });
      var ans = waits.length ? waits.join(' and ') : 'None — all are placed';
      var cands = ['None — all are placed'].concat(procs.map(function (p) { return p + ' K'; }));
      var o = opts(ans, cands.filter(function (c) { return c !== ans; }));
      if (o.length < 4) continue;
      return { q: 'Memory holes (in order): ' + parts.join(' K, ') + ' K. Processes arrive in order: ' + procs.join(' K, ') + ' K. Using ' + algo + ' fit (a hole shrinks after each placement), which process(es) must wait?', o: o, w: res.join('; ') + '.' };
    }
  } };

  /* ===================== DE ===================== */
  function bin(n, w) { var s = n.toString(2); while (w && s.length < w) s = '0' + s; return s; }
  function flipBit(s, i) { return s.slice(0, i) + (s[i] === '0' ? '1' : '0') + s.slice(i + 1); }
  G['de.d2b'] = { s: 'DE', t: 'Number systems', make: function (rng) {
    var r = R(rng), n = r.int(20, 250), fr = r.pick([0, 0.25, 0.5, 0.75, 0.125, 0.375, 0.625]);
    function fb(f) { var s = ''; var k = 0; while (f > 0 && k < 4) { f *= 2; s += f >= 1 ? '1' : '0'; if (f >= 1) f -= 1; k++; } return s; }
    var ans = n.toString(2) + (fr ? '.' + fb(fr) : '');
    var d = [(n + 1).toString(2) + (fr ? '.' + fb(fr) : ''), n.toString(2).split('').reverse().join('').replace(/^0+/, '') + (fr ? '.' + fb(fr) : ''), (n - 2).toString(2) + (fr ? '.' + fb(fr).split('').reverse().join('') : ''), (n ^ 4).toString(2) + (fr ? '.' + fb(fr) : '')];
    return { q: 'Convert (' + (n + fr) + ')₁₀ to binary.', o: opts(ans, d.filter(function (x) { return x !== ans; })), w: 'Integer part: repeated ÷2, remainders bottom-up. Fraction: repeated ×2, integer parts top-down. Answer ' + ans + '.' };
  } };
  G['de.b2ho'] = { s: 'DE', t: 'Number systems', make: function (rng) {
    var r = R(rng), n = r.int(300, 4000), to = r.pick([8, 16]), b = n.toString(2), ans = n.toString(to).toUpperCase();
    var d = [(n + to).toString(to), (n ^ 1).toString(to), (to === 16 ? n.toString(8) : n.toString(16)), n.toString(to).split('').reverse().join('')].map(function (s) { return s.toUpperCase(); });
    return { q: 'Convert (' + b + ')₂ to ' + (to === 8 ? 'octal' : 'hexadecimal') + '.', o: opts(ans, d.filter(function (x) { return x !== ans; })), w: 'Group bits in ' + (to === 8 ? 'threes' : 'fours') + ' from the right: ' + ans + ' (decimal ' + n + ').' };
  } };
  G['de.base'] = { s: 'DE', t: 'Number systems', make: function (rng) {
    var r = R(rng), from = r.pick([3, 4, 5, 6, 7, 12]), to = r.pick([10, 8, 4]); if (to === from) to = 10;
    var n = r.int(40, 400), src = n.toString(from).toUpperCase(), ans = n.toString(to).toUpperCase();
    var d = [(n + 1).toString(to), (n - 1).toString(to), parseInt(src, 10) && to === 10 ? String(parseInt(n.toString(from), 10)) : (n + to).toString(to), n.toString(to).split('').reverse().join('')].map(function (s) { return s.toUpperCase(); });
    return { q: '(' + src + ')' + sub(from) + ' = ( ? )' + sub(to)+'', o: opts(ans, d.filter(function (x) { return x !== ans; })), w: 'Convert to decimal first: ' + n + '. Then to base ' + to + ' by repeated division: ' + ans + '.' };
  } };
  function an(n) { var t = String(n); return (/^8/.test(t) || t === '11' || t === '18') ? 'An ' : 'A '; }
  function sub(n) { return String(n).split('').map(function (c) { return '₀₁₂₃₄₅₆₇₈₉'[+c]; }).join(''); }
  G['de.twos'] = { s: 'DE', t: 'Signed numbers', make: function (rng) {
    var r = R(rng), w = r.pick([8, 6, 5]), lim = Math.pow(2, w - 1), x = r.int(1, lim - 1), ask = r.pick(['rep', 'read']);
    if (ask === 'rep') { var ans = bin((Math.pow(2, w) - x) % Math.pow(2, w), w); var ones = bin(Math.pow(2, w) - 1 - x, w), sm = '1' + bin(x, w - 1);
      return { q: 'Represent −' + x + ' in ' + w + '-bit 2\'s complement.', o: opts(ans, [ones, sm, bin(x, w), bin((Math.pow(2, w) - x + 1) % Math.pow(2, w), w), bin((Math.pow(2, w) - x - 2) % Math.pow(2, w), w)].filter(function (s) { return s !== ans; })), w: '+' + x + ' = ' + bin(x, w) + '; flip → ' + ones + ' (1\'s complement); +1 → ' + ans + '. Sign-magnitude would be ' + sm + '.' }; }
    var v = r.int(Math.pow(2, w - 1), Math.pow(2, w) - 1), s = bin(v, w), val = v - Math.pow(2, w);
    return { q: 'The ' + w + '-bit 2\'s-complement number ' + s + ' represents which decimal value?', o: opts(val, [v, -(v - Math.pow(2, w - 1)), val - 1, -(Math.pow(2, w) - 1 - v)]), w: 'Give the MSB weight −2^' + (w - 1) + ': ' + s + ' = −' + Math.pow(2, w - 1) + ' + ' + (v - Math.pow(2, w - 1)) + ' = ' + val + '.' };
  } };
  G['de.range'] = { s: 'DE', t: 'Signed numbers', make: function (rng) {
    var r = R(rng), n = r.pick([4, 5, 6, 8, 10, 12, 16]), rep = r.pick(['2c', 'sm', 'us']), h = Math.pow(2, n - 1);
    var a = { '2c': '−' + h + ' to +' + (h - 1), sm: '−' + (h - 1) + ' to +' + (h - 1), us: '0 to ' + (2 * h - 1) };
    var name = { '2c': "2's complement", sm: 'sign-magnitude (or 1\'s complement)', us: 'unsigned' };
    var o = [a[rep]]; ['2c', 'sm', 'us'].forEach(function (k) { if (k !== rep) o.push(a[k]); }); o.push('−' + (2 * h) + ' to +' + (2 * h - 1));
    return { q: 'Range of ' + an(n).toLowerCase() + n + '-bit ' + name[rep] + ' number?', o: o, w: '2\'s complement: −2ⁿ⁻¹ to 2ⁿ⁻¹ − 1. Sign-magnitude / 1\'s: ±(2ⁿ⁻¹ − 1). Unsigned: 0 to 2ⁿ − 1.' };
  } };
  G['de.sub'] = { s: 'DE', t: 'Signed numbers', make: function (rng) {
    var r = R(rng), w = 8, a = r.int(5, 100), b = r.int(5, 100), res = a - b, M = 256;
    var ans = bin(((res % M) + M) % M, w);
    return { q: 'Using 8-bit 2\'s-complement arithmetic, compute ' + a + ' − ' + b + ' (' + bin(a, 8) + ' − ' + bin(b, 8) + '). The 8-bit result is:', o: opts(ans, [bin(((a + b) % M), 8), bin(((-res % M) + M) % M, 8), bin((((res - 1) % M) + M) % M, 8)].filter(function (s) { return s !== ans; }), function (k) { return bin((((res + k + 1) % M) + M) % M, 8); }), w: 'A + (2\'s complement of B) = ' + bin(a, 8) + ' + ' + bin((M - b) % M, 8) + ', discard the end carry → ' + ans + ' = ' + res + '.' };
  } };
  G['de.gray'] = { s: 'DE', t: 'Codes', make: function (rng) {
    var r = R(rng), w = r.int(4, 7), n = r.int(Math.pow(2, w - 1), Math.pow(2, w) - 1), dir = r.pick(['b2g', 'g2b']);
    var g = n ^ (n >> 1);
    if (dir === 'b2g') { var ans = bin(g, w); return { q: 'Convert binary ' + bin(n, w) + ' to Gray code.', o: opts(ans, [bin(n ^ (n << 1) & (Math.pow(2, w) - 1), w), bin(~n & (Math.pow(2, w) - 1), w), bin(g ^ 1, w), bin(n, w)].filter(function (s) { return s !== ans; })), w: 'Keep the MSB; each next Gray bit = binary bit ⊕ the binary bit to its left → ' + ans + '.' }; }
    var b = 0, x = g; while (x) { b ^= x; x >>= 1; }
    var ans2 = bin(b, w);
    return { q: 'Convert Gray code ' + bin(g, w) + ' to binary.', o: opts(ans2, [bin(g ^ (g >> 1), w), bin(g, w), bin(b ^ 1, w), bin(~b & (Math.pow(2, w) - 1), w)].filter(function (s) { return s !== ans2; })), w: 'Keep the MSB; each next binary bit = previous BINARY bit ⊕ current Gray bit → ' + ans2 + '.' };
  } };
  G['de.bcd'] = { s: 'DE', t: 'Codes', make: function (rng) {
    var r = R(rng), n = r.int(10, 999), code = r.pick(['bcd', 'xs3']), ds = String(n).split('');
    function enc(off) { return ds.map(function (d) { return bin(+d + off, 4); }).join(' '); }
    var ans = code === 'bcd' ? enc(0) : enc(3);
    var d = [code === 'bcd' ? enc(3) : enc(0), n.toString(2), ds.map(function (d) { return bin((+d ^ (+d >> 1)), 4); }).join(' '), ds.slice().reverse().map(function (d) { return bin(+d + (code === 'bcd' ? 0 : 3), 4); }).join(' '), enc(6 % 7 === 6 ? 1 : 1), enc(code === 'bcd' ? 1 : 2)];
    return { q: 'Write (' + n + ')₁₀ in ' + (code === 'bcd' ? 'BCD (8421)' : 'Excess-3 code') + '.', o: opts(ans, d.filter(function (s) { return s !== ans; })), w: (code === 'bcd' ? 'Each decimal digit → 4-bit binary.' : 'Excess-3 = BCD of each digit + 0011.') + ' ' + ans + '.' };
  } };

  /* --- Boolean minimisation (exact, for 3–4 variables) --- */
  function primeImplicants(n, ones, dc) {
    var terms = ones.concat(dc).map(function (m) { return { v: m, mask: 0 }; }), primes = [], seen = {};
    while (terms.length) {
      var next = [], used = {}, key = {};
      for (var i = 0; i < terms.length; i++) for (var j = i + 1; j < terms.length; j++) {
        var a = terms[i], b = terms[j];
        if (a.mask !== b.mask) continue; var d = a.v ^ b.v; if (d & (d - 1)) continue; if ((a.v & ~a.mask) === (b.v & ~b.mask) && d === 0) continue;
        var t = { v: a.v & ~d, mask: a.mask | d }, k = t.v + ':' + t.mask; used[i] = used[j] = 1; if (!key[k]) { key[k] = 1; next.push(t); }
      }
      terms.forEach(function (t, i) { var k = t.v + ':' + t.mask; if (!used[i] && !seen[k]) { seen[k] = 1; primes.push(t); } });
      terms = next;
    }
    return primes;
  }
  function covers(t, m) { return (m & ~t.mask) === (t.v & ~t.mask); }
  function lits(t, n) { var c = 0; for (var i = 0; i < n; i++) if (!(t.mask >> i & 1)) c++; return c; }
  function minCover(n, ones, dc) {
    if (!ones.length) return [];
    var P = primeImplicants(n, ones, dc), best = null, bestCost = 1e9;
    var k = P.length;
    // exhaustive over subsets ordered by size (k is small for 4 vars)
    for (var size = 1; size <= k && !best; size++) {
      (function rec(start, chosen) {
        if (chosen.length === size) { if (ones.every(function (m) { return chosen.some(function (t) { return covers(t, m); }); })) { var cost = chosen.reduce(function (s, t) { return s + lits(t, n); }, 0); if (cost < bestCost) { bestCost = cost; best = chosen.slice(); } } return; }
        for (var i = start; i < k; i++) { chosen.push(P[i]); rec(i + 1, chosen); chosen.pop(); }
      })(0, []);
    }
    return best;
  }
  var VN = ['A', 'B', 'C', 'D'];
  function termStr(t, n, pos) {
    var s = []; for (var i = 0; i < n; i++) { var bit = n - 1 - i; if (t.mask >> bit & 1) continue; var one = t.v >> bit & 1; if (!pos) s.push(VN[i] + (one ? '' : "'")); else s.push(VN[i] + (one ? "'" : '')); }
    if (!s.length) return pos ? '0' : '1';
    return pos ? (s.length > 1 ? '(' + s.join(' + ') + ')' : s[0]) : s.join('');
  }
  function exprStr(cover, n, pos) { if (!cover.length) return pos ? '1' : '0'; var ts = cover.map(function (t) { return termStr(t, n, pos); }).sort(); return pos ? ts.join('') : ts.join(' + '); }
  function evalCover(cover, m) { return cover.some(function (t) { return covers(t, m); }); }
  G['de.kmap'] = { s: 'DE', t: 'K-map', make: function (rng) {
    var r = R(rng);
    for (var tries = 0; tries < 300; tries++) {
      var n = r.pick([3, 4, 4]), N = 1 << n, pos = r.int(0, 2) === 0, useDc = n === 4 && r.int(0, 2) === 0;
      var all = []; for (var i = 0; i < N; i++) all.push(i); all = r.shuffle(all);
      var k1 = r.int(Math.floor(N * 0.3), Math.floor(N * 0.6)), ones = all.slice(0, k1).sort(function (a, b) { return a - b; });
      var dc = useDc ? all.slice(k1, k1 + r.int(1, 3)).sort(function (a, b) { return a - b; }) : [];
      var zeros = []; for (var z = 0; z < N; z++) if (ones.indexOf(z) < 0 && dc.indexOf(z) < 0) zeros.push(z);
      var cover = pos ? minCover(n, zeros, dc) : minCover(n, ones, dc);
      if (!cover || cover.length < 2) continue;
      var ans = exprStr(cover, n, pos);
      // distractors: minimal forms of nearby functions (flip one minterm) — never equivalent on the care set
      var ds = [], used = {}; used[ans] = 1;
      for (var a = 0; a < 40 && ds.length < 3; a++) {
        var flip = r.pick(ones.concat(zeros)), o2 = ones.slice(), z2 = zeros.slice();
        if (o2.indexOf(flip) >= 0) { o2.splice(o2.indexOf(flip), 1); z2.push(flip); } else { z2.splice(z2.indexOf(flip), 1); o2.push(flip); }
        var c2 = pos ? minCover(n, z2, dc) : minCover(n, o2, dc); if (!c2) continue;
        var s2 = exprStr(c2, n, pos);
        // check it differs from the true function on some care cell
        var differs = ones.concat(zeros).some(function (m) { var truth = ones.indexOf(m) >= 0; var v = pos ? !evalCover(c2, m) : evalCover(c2, m); return v !== truth; });
        if (differs && !used[s2]) { used[s2] = 1; ds.push(s2); }
      }
      if (ds.length < 3) continue;
      var fn = 'F(' + VN.slice(0, n).join(', ') + ') = ' + (pos ? 'ΠM(' + zeros.join(', ') + ')' : 'Σm(' + ones.join(', ') + ')') + (dc.length ? ' + d(' + dc.join(', ') + ')' : '');
      return { q: 'Minimal ' + (pos ? 'POS' : 'SOP') + ' form of ' + fn + '?', o: [ans].concat(ds), w: 'Group the ' + (pos ? '0s' : '1s') + ' (Gray order 00, 01, 11, 10; edges wrap' + (dc.length ? '; use don\'t-cares only if they enlarge a group' : '') + '). Groups: ' + cover.map(function (t) { return termStr(t, n, pos); }).join(', ') + '. Other options are minimal forms of functions that differ in at least one cell.' };
    }
  } };
  G['de.minterms'] = { s: 'DE', t: 'SOP/POS', make: function (rng) {
    var r = R(rng);
    for (var t = 0; t < 100; t++) {
      var n = 3, terms = [], k = r.int(2, 3);
      for (var i = 0; i < k; i++) { var mask = r.pick([1, 2, 4, 0]), v = r.int(0, 7) & ~mask; terms.push({ v: v, mask: mask }); }
      var ones = []; for (var m = 0; m < 8; m++) if (terms.some(function (tt) { return covers(tt, m); })) ones.push(m);
      if (ones.length < 2 || ones.length > 6) continue;
      var e = terms.map(function (tt) { return termStr(tt, 3, false); }).join(' + ');
      var zeros = [0, 1, 2, 3, 4, 5, 6, 7].filter(function (m) { return ones.indexOf(m) < 0; });
      var ans = 'Σm(' + ones.join(', ') + ')';
      var d = ['Σm(' + zeros.join(', ') + ')', 'Σm(' + ones.map(function (m) { return 7 - m; }).sort(function (a, b) { return a - b; }).join(', ') + ')', 'Σm(' + ones.slice(0, -1).join(', ') + ')', 'Σm(' + ones.concat([zeros[0]]).sort(function (a, b) { return a - b; }).join(', ') + ')'];
      var o = opts(ans, d.filter(function (s) { return s !== ans; }));
      if (o.length < 4) continue;
      return { q: 'F(A, B, C) = ' + e + '. Which is its canonical SOP?', o: o, w: 'Expand each term over the missing variables. Its POS is ΠM(' + zeros.join(', ') + ').' };
    }
  } };
  G['de.mux'] = { s: 'DE', t: 'MUX/Decoder', make: function (rng) {
    var r = R(rng), ask = r.pick(['mux', 'dec', 'sel']);
    if (ask === 'mux') { var big = r.pick([8, 16, 32, 64, 128, 256]), small = r.pick([2, 4]); if (small === 4 && [8, 32, 128].indexOf(big) >= 0) big *= 2; var c = 0, x = big; while (x > 1) { x /= small; c += x; }
      return { q: 'How many ' + small + '×1 multiplexers are needed to build ' + an(big).toLowerCase() + big + '×1 multiplexer?', o: opts(c, [big / small, c + 1, big - 1 === c ? c - 1 : big - 1]), w: 'Count level by level: ' + big + '/' + small + ' + … + 1 = ' + c + '.' }; }
    if (ask === 'dec') { var bigd = r.pick([4, 5, 6]), sm = r.pick([2, 3]); if (sm >= bigd) sm = 2; var outs = 1 << bigd, so = 1 << sm; var first = outs / so; var lvl = bigd - sm; var cnt = first, cur = first; while (cur > 1) { cur = Math.ceil(cur / so); cnt += cur; }
      var leaf = outs / so; var levels = []; var tot = 0, need = leaf; while (need >= 1) { tot += need; if (need === 1) break; need = Math.ceil(need / so); }
      return { q: 'Building a ' + bigd + '-to-' + outs + ' decoder from ' + sm + '-to-' + so + ' decoders (with enable) in a tree, how many smaller decoders are needed?', o: opts(tot, [leaf, tot + 1, outs / 2]), w: 'Leaf level: ' + outs + '/' + so + ' = ' + leaf + ' decoders; upper levels drive their enables. Total = ' + tot + '.' }; }
    var n = r.pick([4, 8, 16, 32, 64]); return { q: an(n) + n + '×1 multiplexer needs how many select lines?', o: opts(Math.log2(n), [n / 2, n, Math.log2(n) + 1]), w: '2^s = ' + n + ' → s = ' + Math.log2(n) + '.' };
  } };
  G['de.counter'] = { s: 'DE', t: 'Counters', make: function (rng) {
    var r = R(rng), ask = r.pick(['ff', 'state', 'ring', 'freq']);
    if (ask === 'ff') { var N = r.int(5, 200); var k = Math.ceil(Math.log2(N)); return { q: 'Minimum number of flip-flops for a mod-' + N + ' counter?', o: opts(k, [k + 1, k - 1, N]), w: 'Smallest k with 2^k ≥ ' + N + ' → ' + k + '.' }; }
    if (ask === 'state') { var M = r.int(5, 16), p = r.int(20, 300); return { q: 'A mod-' + M + ' counter starts at 0. What is its count after ' + p + ' clock pulses?', o: opts(p % M, [(p + 1) % M, (p - 1 + M) % M, Math.floor(p / M) % M]), w: p + ' mod ' + M + ' = ' + (p % M) + '.' }; }
    if (ask === 'ring') { var n = r.int(3, 8), typ = r.pick(['ring', 'Johnson']); var ans = typ === 'ring' ? n : 2 * n; return { q: 'How many states does a ' + n + '-flip-flop ' + typ + ' counter have, and how many states are unused?', o: [ans + ' states, ' + (Math.pow(2, n) - ans) + ' unused', (typ === 'ring' ? 2 * n : n) + ' states, ' + (Math.pow(2, n) - (typ === 'ring' ? 2 * n : n)) + ' unused', Math.pow(2, n) + ' states, 0 unused', (n - 1) + ' states, ' + (Math.pow(2, n) - n + 1) + ' unused'], w: 'Ring: n states; Johnson (twisted ring): 2n states. Unused = 2ⁿ − used.' }; }
    var bits = r.int(4, 12), tpd = r.pick([5, 10, 20, 25, 50]); var T = bits * tpd, f = 1000 / T;
    return { q: an(bits) + bits + '-bit ripple counter uses flip-flops with ' + tpd + ' ns propagation delay each. Maximum clock frequency (MHz) without skipping counts?', o: opts(f, [1000 / tpd, f * 2, f / 2]), w: 'Total ripple delay = ' + bits + ' × ' + tpd + ' = ' + T + ' ns; f_max = 1/' + T + ' ns = ' + fmt(f) + ' MHz.' };
  } };
  G['de.ripple'] = { s: 'DE', t: 'Adders', make: function (rng) {
    var r = R(rng), n = r.pick([4, 8, 16, 32]), tc = r.pick([2, 3, 5, 10]), ts = tc + r.pick([1, 2, 3]);
    var ans = (n - 1) * tc + ts;
    return { q: an(n) + n + '-bit ripple-carry adder uses full adders with carry delay ' + tc + ' ns and sum delay ' + ts + ' ns. Worst-case time until the final sum bit is valid?', o: opts(ans, [n * tc, n * ts, n * tc + ts]), w: 'The carry ripples through ' + (n - 1) + ' stages (' + (n - 1) + ' × ' + tc + ' ns), then the last stage forms its sum (' + ts + ' ns): ' + ans + ' ns.' };
  } };
  G['de.jk'] = { s: 'DE', t: 'Flip-flops', make: function (rng) {
    var r = R(rng), typ = r.pick(['JK', 'T', 'SR', 'D']), q = r.int(0, 1), seq = [], k = r.int(3, 5), Q = q, trace = [];
    for (var i = 0; i < k; i++) {
      var inp;
      if (typ === 'JK') { inp = [r.int(0, 1), r.int(0, 1)]; var J = inp[0], K = inp[1]; Q = J && K ? 1 - Q : J ? 1 : K ? 0 : Q; seq.push('JK=' + J + K); }
      else if (typ === 'SR') { do { inp = [r.int(0, 1), r.int(0, 1)]; } while (inp[0] && inp[1]); Q = inp[0] ? 1 : inp[1] ? 0 : Q; seq.push('SR=' + inp[0] + inp[1]); }
      else if (typ === 'T') { inp = r.int(0, 1); Q = inp ? 1 - Q : Q; seq.push('T=' + inp); }
      else { inp = r.int(0, 1); Q = inp; seq.push('D=' + inp); }
      trace.push(Q);
    }
    var ans = trace.join(''), d = [trace.map(function (x) { return 1 - x; }).join(''), (q + '' + trace.slice(0, -1).join('')), trace.slice().reverse().join('')];
    var o = opts(ans, d.filter(function (s) { return s !== ans; }), function (j) { return flipBit(ans, (j - 1) % ans.length); });
    return { q: 'A ' + typ + ' flip-flop starts with Q = ' + q + '. Clock pulses are applied with inputs ' + seq.join(', ') + '. What is Q after each pulse?', o: o, w: typ + ': ' + ({ JK: '00 hold, 01 reset, 10 set, 11 toggle', T: '0 hold, 1 toggle', SR: '00 hold, 01 reset, 10 set', D: 'Q follows D' })[typ] + '. Sequence: ' + ans + '.' };
  } };
  G['de.funcs'] = { s: 'DE', t: 'Boolean algebra', make: function (rng) {
    var r = R(rng), n = r.int(2, 4), ask = r.pick(['all', 'sd', 'rows']);
    var all = Math.pow(2, Math.pow(2, n)), sd = Math.pow(2, Math.pow(2, n - 1)), rows = Math.pow(2, n);
    if (ask === 'all') return { q: 'How many distinct Boolean functions of ' + n + ' variables are there?', o: opts(all, [rows, sd, n * n === rows ? Math.pow(n, n) : n * n]), w: '2^(2ⁿ) = 2^' + rows + ' = ' + all + '.' };
    if (ask === 'sd') return { q: 'How many self-dual Boolean functions of ' + n + ' variables are there?', o: opts(sd, [all, rows, sd * 2]), w: '2^(2ⁿ⁻¹) = 2^' + (rows / 2) + ' = ' + sd + '.' };
    return { q: 'A truth table for ' + n + ' input variables has how many rows?', o: opts(rows, [2 * n, all, n * n === rows ? rows + 2 : n * n]), w: '2ⁿ = ' + rows + '.' };
  } };
  G['de.sisoreg'] = { s: 'DE', t: 'Registers', make: function (rng) {
    var r = R(rng), n = r.int(4, 16), typ = r.pick(['SISO', 'SIPO', 'PISO', 'PIPO']);
    var v = { SISO: 2 * n - 1, SIPO: n, PISO: n, PIPO: 1 }[typ];
    return { q: an(n) + n + '-bit ' + typ + ' shift register: how many clock pulses are needed to load ' + n + ' bits and read all of them out?', o: opts(v, [2 * n, n, 1, n - 1, 2 * n - 1].filter(function (x) { return x !== v; })), w: 'SISO 2n − 1; SIPO n (n in, 0 out); PISO n (1 in, n − 1 out); PIPO 1.' };
  } };
  G['de.ieee'] = { s: 'DE', t: 'Floating point', make: function (rng) {
    var r = R(rng), e = r.int(-6, 8), frac = r.pick([0, 0.5, 0.25, 0.75, 0.125, 0.625]), sign = r.int(0, 1);
    var val = (1 + frac) * Math.pow(2, e) * (sign ? -1 : 1), E = e + 127;
    var ans = 'S = ' + sign + ', E = ' + bin(E, 8);
    return { q: 'In IEEE 754 single precision, what are the sign bit and the 8-bit exponent field for ' + val + '?', o: opts(ans, ['S = ' + sign + ', E = ' + bin(e + 128, 8), 'S = ' + (1 - sign) + ', E = ' + bin(E, 8), 'S = ' + sign + ', E = ' + bin((e + 126 + 256) % 256, 8), 'S = ' + sign + ', E = ' + bin(((e % 256) + 256) % 256, 8)]), w: val + ' = ' + (sign ? '−' : '') + (1 + frac) + ' × 2^' + e + ' (normalised 1.M form). E = ' + e + ' + 127 = ' + E + ' = ' + bin(E, 8) + '.' };
  } };

  G['de.kmap2'] = { s: 'DE', t: 'K-map', make: function (rng) { return G['de.kmap'].make(rng); } };
  G['de.excit'] = { s: 'DE', t: 'Flip-flops', make: function (rng) {
    var r = R(rng), typ = r.pick(['JK', 'SR', 'T', 'D']), a = r.int(0, 1), b = r.int(0, 1);
    var tbl = { JK: ['J=0, K=X', 'J=1, K=X', 'J=X, K=1', 'J=X, K=0'], SR: ['S=0, R=X', 'S=1, R=0', 'S=0, R=1', 'S=X, R=0'], T: ['T=0', 'T=1', 'T=1', 'T=0'], D: ['D=0', 'D=1', 'D=0', 'D=1'] };
    var idx = a * 2 + b, ans = tbl[typ][idx];
    var pool = { JK: ['J=0, K=X', 'J=1, K=X', 'J=X, K=1', 'J=X, K=0', 'J=1, K=1', 'J=0, K=0'], SR: ['S=0, R=X', 'S=1, R=0', 'S=0, R=1', 'S=X, R=0', 'S=1, R=1', 'S=X, R=1'], T: ['T=0', 'T=1', 'T=X', 'T=Q'], D: ['D=0', 'D=1', 'D=X', "D=Q'"] }[typ];
    var o = [ans]; r.shuffle(pool).forEach(function (p) { if (o.length < 4 && o.indexOf(p) < 0) o.push(p); });
    return { q: 'Excitation table: for a ' + typ + ' flip-flop to go from Qn = ' + a + ' to Qn+1 = ' + b + ', the inputs must be:', o: o, w: { JK: 'JK: 0→0 0X, 0→1 1X, 1→0 X1, 1→1 X0.', SR: 'SR: 0→0 0X, 0→1 10, 1→0 01, 1→1 X0.', T: 'T = 1 whenever the state changes.', D: 'D = the next state.' }[typ] };
  } };
  G['de.arith'] = { s: 'DE', t: 'Number systems', make: function (rng) {
    var r = R(rng), base = r.pick([2, 8, 16]), a = r.int(base === 2 ? 5 : 30, base === 2 ? 60 : 900), b = r.int(base === 2 ? 5 : 30, base === 2 ? 60 : 900), s = a + b;
    var f = function (x) { return x.toString(base).toUpperCase(); };
    return { q: 'Add (' + f(a) + ')' + sub(base) + ' + (' + f(b) + ')' + sub(base) + ' in base ' + base + '.', o: opts(f(s), [f(s + 1), f(a ^ b), String(parseInt(f(a), 10) + parseInt(f(b), 10)) === f(s) ? f(s + base) : String(parseInt(f(a), 10) + parseInt(f(b), 10))].filter(function (x) { return x !== f(s) && !/NaN/.test(x); }), function (k) { return f(s + k * base); }), w: 'Decimal ' + a + ' + ' + b + ' = ' + s + ' = (' + f(s) + ')' + sub(base) + '. Carry when a column reaches ' + base + '.' };
  } };

  root.SnowGens = { G: G, mulberry32: mulberry32, _t: { sched: sched, pr: pr, disk: disk, minCover: minCover, lits: lits } };
})(typeof window !== 'undefined' ? window : globalThis);
/* DBMS generators — appended into gens.js */
(function (root) {
  'use strict';
  var SG = root.SnowGens, G = SG.G;
  function R(rng) { return { int: function (a, b) { return a + Math.floor(rng() * (b - a + 1)); }, pick: function (a) { return a[Math.floor(rng() * a.length)]; }, shuffle: function (a) { a = a.slice(); for (var i = a.length - 1; i > 0; i--) { var j = Math.floor(rng() * (i + 1)); var t = a[i]; a[i] = a[j]; a[j] = t; } return a; } }; }
  function uniq4(correct, cands) { var o = [correct]; cands.forEach(function (c) { if (o.length < 4 && c != null && o.indexOf(c) < 0) o.push(c); }); return o.length === 4 ? o : null; }
  var L = 'ABCDEF';
  function str(mask, n) { var s = ''; for (var i = 0; i < n; i++) if (mask >> i & 1) s += L[i]; return s || '∅'; }
  function closure(x, F) { var c = x, ch = true; while (ch) { ch = false; F.forEach(function (f) { if ((f[0] & c) === f[0] && (f[1] & ~c)) { c |= f[1]; ch = true; } }); } return c; }
  function popc(m) { var c = 0; while (m) { c += m & 1; m >>= 1; } return c; }
  function keys(n, F) { var all = (1 << n) - 1, ks = []; for (var m = 1; m <= all; m++) { if (closure(m, F) !== all) continue; if (ks.some(function (k) { return (k & m) === k; })) continue; ks.push(m); } return ks; }
  // keys() iterates masks in increasing numeric order which is not by size; fix minimality by filtering
  function candKeys(n, F) { var all = (1 << n) - 1, sk = []; for (var m = 1; m <= all; m++) if (closure(m, F) === all) sk.push(m); return sk.filter(function (m) { return !sk.some(function (o) { return o !== m && (o & m) === o; }); }); }
  function randF(r, n, k) { var F = [], tries = 0; while (F.length < k && tries++ < 100) { var lhs = 0, sz = r.int(1, 2); while (popc(lhs) < sz) lhs |= 1 << r.int(0, n - 1); var rhs = 0; while (!rhs) { var b = 1 << r.int(0, n - 1); if (!(b & lhs)) rhs |= b; } if (r.int(0, 3) === 0) { var b2 = 1 << r.int(0, n - 1); if (!(b2 & lhs)) rhs |= b2; } F.push([lhs, rhs]); } return F; }
  function fdStr(F, n) { return '{' + F.map(function (f) { return str(f[0], n) + ' → ' + str(f[1], n); }).join(', ') + '}'; }
  function rel(n) { return 'R(' + L.slice(0, n).split('').join(', ') + ')'; }
  function nf(n, F) {
    var all = (1 << n) - 1, ks = candKeys(n, F), prime = ks.reduce(function (a, k) { return a | k; }, 0);
    var split = []; F.forEach(function (f) { for (var i = 0; i < n; i++) if ((f[1] >> i & 1) && !(f[0] >> i & 1)) split.push([f[0], 1 << i]); });
    var bc = split.every(function (f) { return closure(f[0], F) === all; });
    if (bc) return { nf: 'BCNF', ks: ks, prime: prime };
    var t3 = split.every(function (f) { return closure(f[0], F) === all || (f[1] & prime); });
    if (t3) return { nf: '3NF', ks: ks, prime: prime };
    var two = true; ks.forEach(function (k) { for (var s = (k - 1) & k; s > 0; s = (s - 1) & k) { var c = closure(s, F) & ~s & ~prime; if (c) two = false; } });
    return { nf: two ? '2NF' : '1NF', ks: ks, prime: prime };
  }
  G['db.closure'] = { s: 'DBMS', t: 'Functional dependency', make: function (rng) {
    var r = R(rng);
    for (var t = 0; t < 200; t++) {
      var n = r.int(5, 6), F = randF(r, n, r.int(3, 5)), x = 0; while (popc(x) < r.int(1, 2)) x |= 1 << r.int(0, n - 1);
      var c = closure(x, F); if (c === x) continue;
      var miss = (~c) & ((1 << n) - 1), cands = [];
      for (var i = 0; i < n; i++) { if ((c >> i & 1) && !(x >> i & 1)) cands.push(str(c & ~(1 << i), n)); if (miss >> i & 1) cands.push(str(c | 1 << i, n)); }
      var o = uniq4(str(c, n), r.shuffle(cands)); if (!o) continue;
      return { q: rel(n) + ', F = ' + fdStr(F, n) + '. What is ' + str(x, n) + '⁺ (the closure of ' + str(x, n) + ')?', o: o, w: 'Start with ' + str(x, n) + ' and keep adding the right side of any FD whose left side is already inside, until nothing changes: ' + str(c, n) + '.' };
    }
  } };
  G['db.ckey'] = { s: 'DBMS', t: 'Keys', make: function (rng) {
    var r = R(rng);
    for (var t = 0; t < 300; t++) {
      var n = r.int(4, 6), F = randF(r, n, r.int(3, 5)), ks = candKeys(n, F), all = (1 << n) - 1;
      if (ks.length < 1 || ks.every(function (k) { return k === all; })) continue;
      var k = r.pick(ks); if (popc(k) > 3) continue;
      var wrong = [];
      for (var m = 1; m <= all; m++) { if (ks.indexOf(m) >= 0 || popc(m) > 3) continue; wrong.push(m); }
      wrong = r.shuffle(wrong).slice(0, 3);
      if (wrong.length < 3) continue;
      var o = uniq4(str(k, n), wrong.map(function (m) { return str(m, n); })); if (!o) continue;
      return { q: rel(n) + ', F = ' + fdStr(F, n) + '. Which of these is a candidate key?', o: o, w: 'Candidate keys: ' + ks.map(function (x) { return str(x, n); }).join(', ') + '. A candidate key\'s closure is all attributes and no proper subset\'s is. Tip: attributes never on any right-hand side must be in every key.' };
    }
  } };
  G['db.nf'] = { s: 'DBMS', t: 'Normalization', make: function (rng) {
    var r = R(rng), want = r.pick(['1NF', '2NF', '3NF', 'BCNF']);
    for (var t = 0; t < 500; t++) {
      var n = r.int(4, 5), F = randF(r, n, r.int(2, 4)), res = nf(n, F);
      if (res.nf !== want && t < 450) continue;
      var o = ['1NF', '2NF', '3NF', 'BCNF']; o.splice(o.indexOf(res.nf), 1); o.unshift(res.nf);
      var why = { BCNF: 'Every determinant is a super key.', '3NF': 'Some FD has a non-super-key left side, but its right side is prime, so 3NF holds but BCNF fails.', '2NF': 'No non-prime attribute depends on part of a key, but a non-key determines a non-prime attribute (transitive dependency).', '1NF': 'A non-prime attribute depends on a proper subset of a candidate key (partial dependency).' }[res.nf];
      return { q: rel(n) + ' with F = ' + fdStr(F, n) + '. What is the highest normal form of R (assume it is in 1NF)?', o: o, w: 'Candidate keys: ' + res.ks.map(function (x) { return str(x, n); }).join(', ') + '; prime attributes: ' + str(res.prime, n) + '. ' + why };
    }
  } };
  G['db.lossless'] = { s: 'DBMS', t: 'Normalization', make: function (rng) {
    var r = R(rng);
    for (var t = 0; t < 200; t++) {
      var n = r.int(4, 5), all = (1 << n) - 1, F = randF(r, n, r.int(2, 4));
      var a = 0, b = 0; for (var i = 0; i < n; i++) { var z = r.int(0, 2); if (z === 0) a |= 1 << i; else if (z === 1) b |= 1 << i; else { a |= 1 << i; b |= 1 << i; } }
      if (!a || !b || a === all || b === all) continue;
      var com = a & b, ll = com && ((closure(com, F) & a) === a || (closure(com, F) & b) === b);
      var ans = ll ? 'Lossless' : 'Lossy';
      return { q: rel(n) + ', F = ' + fdStr(F, n) + ' is decomposed into R1(' + str(a, n).split('').join(', ') + ') and R2(' + str(b, n).split('').join(', ') + '). The decomposition is:', o: [ans, ll ? 'Lossy' : 'Lossless', 'Lossless only if R1 has a primary key', 'Cannot be decided without data'], w: 'Common attributes: ' + str(com, n) + (com ? ', closure ' + str(closure(com, F), n) : '') + '. Lossless iff the common attributes form a super key of R1 or of R2.' + (ll ? '' : ' Here they don\'t, so joining back creates spurious tuples.') };
    }
  } };
  G['db.superkeys'] = { s: 'DBMS', t: 'Keys', make: function (rng) {
    var r = R(rng), n = r.int(4, 6), case_ = r.pick(['one', 'two', 'pair']);
    var all = (1 << n) - 1, ks;
    if (case_ === 'one') ks = [1]; else if (case_ === 'two') ks = [1, 2]; else ks = [3, 4];
    var cnt = 0; for (var m = 1; m <= all; m++) if (ks.some(function (k) { return (k & m) === k; })) cnt++;
    var desc = ks.map(function (k) { return str(k, n); }).join(' and ');
    return { q: 'Relation ' + rel(n) + ' has ' + n + ' attributes. Its only candidate key' + (ks.length > 1 ? 's are ' : ' is ') + desc + '. How many super keys does it have?', o: uniq4(String(cnt), [String(Math.pow(2, n - 1)), String(Math.pow(2, n) - 1), String(cnt + Math.pow(2, n - 3)), String(cnt - 1), String(Math.pow(2, n - 2))]), w: (case_ === 'one' ? 'Any set containing A: 2^(n−1) = ' + cnt + '.' : 'Inclusion–exclusion: supersets of the first key + supersets of the second − supersets of both = ' + cnt + '.') };
  } };
  G['db.serial'] = { s: 'DBMS', t: 'Transactions', make: function (rng) {
    var r = R(rng);
    for (var t = 0; t < 300; t++) {
      var nt = r.int(2, 3), items = ['A', 'B'], ops = [];
      for (var i = 1; i <= nt; i++) { var k = r.int(2, 3); for (var j = 0; j < k; j++) ops.push({ t: i, op: r.pick(['R', 'W']), x: r.pick(items) }); }
      var sch = r.shuffle(ops);
      // keep each transaction's internal order as shuffled; build precedence graph
      var E = {}; for (var a = 0; a < sch.length; a++) for (var b = a + 1; b < sch.length; b++) { var p = sch[a], q = sch[b]; if (p.t !== q.t && p.x === q.x && (p.op === 'W' || q.op === 'W')) E[p.t + '>' + q.t] = 1; }
      var edges = Object.keys(E);
      // topological sort
      var indeg = {}, ord = []; for (i = 1; i <= nt; i++) indeg[i] = 0; edges.forEach(function (e) { indeg[+e.split('>')[1]]++; });
      var avail = Object.keys(indeg).filter(function (v) { return !indeg[v]; }).map(Number), rem = JSON.parse(JSON.stringify(indeg)), out = [];
      var cyc = false; var used = {};
      while (out.length < nt) { var c = []; for (i = 1; i <= nt; i++) if (!used[i] && rem[i] === 0) c.push(i); if (!c.length) { cyc = true; break; } if (c.length > 1) { cyc = 'multi'; } var v = c[0]; used[v] = 1; out.push(v); edges.forEach(function (e) { if (+e.split('>')[0] === v) rem[+e.split('>')[1]]--; }); }
      if (cyc === 'multi') continue; // ambiguous serial order — regenerate for a unique answer
      var s = sch.map(function (o) { return o.op + o.t + '(' + o.x + ')'; }).join('; ');
      var ans = cyc === true ? 'Not conflict serializable' : 'Serializable as ' + out.map(function (v) { return 'T' + v; }).join(' → ');
      var perms = nt === 2 ? [[1, 2], [2, 1]] : [[1, 2, 3], [1, 3, 2], [2, 1, 3], [2, 3, 1], [3, 1, 2], [3, 2, 1]];
      var c2 = perms.map(function (p) { return 'Serializable as ' + p.map(function (v) { return 'T' + v; }).join(' → '); }).filter(function (x) { return x !== ans; });
      if (cyc !== true) c2.unshift('Not conflict serializable');
      var o = uniq4(ans, r.shuffle(c2).sort(function (x, y) { return (y === 'Not conflict serializable') - (x === 'Not conflict serializable'); }));
      if (!o) continue;
      return { q: 'Schedule: ' + s + '. Is it conflict serializable, and if so, equivalent to which serial order?', o: o, w: 'Conflicting pairs (different transactions, same item, at least one write) give edges: ' + (edges.length ? edges.map(function (e) { return 'T' + e.replace('>', '→T'); }).join(', ') : 'none') + '. ' + (cyc === true ? 'The precedence graph has a cycle.' : 'No cycle; topological order ' + out.map(function (v) { return 'T' + v; }).join(' → ') + '.') };
    }
  } };
  G['db.product'] = { s: 'DBMS', t: 'Relational algebra', make: function (rng) {
    var r = R(rng), m = r.int(3, 40), n = r.int(3, 40), da = r.int(2, 6), db = r.int(2, 6), ask = r.pick(['prod', 'union', 'inter', 'diff']);
    if (ask === 'prod') return { q: 'R has ' + m + ' tuples and ' + da + ' attributes; S has ' + n + ' tuples and ' + db + ' attributes. R × S has how many tuples and attributes?', o: uniq4((m * n) + ' tuples, ' + (da + db) + ' attributes', [(m + n) + ' tuples, ' + (da + db) + ' attributes', (m * n) + ' tuples, ' + (da * db) + ' attributes', Math.max(m, n) + ' tuples, ' + (da + db) + ' attributes', (m * n) + ' tuples, ' + Math.max(da, db) + ' attributes']), w: 'Cartesian product pairs every tuple: m × n; degrees add.' };
    var lo, hi, nm;
    if (ask === 'union') { lo = Math.max(m, n); hi = m + n; nm = 'R ∪ S'; }
    else if (ask === 'inter') { lo = 0; hi = Math.min(m, n); nm = 'R ∩ S'; }
    else { lo = 0; hi = m; nm = 'R − S'; }
    var ans = lo + ' to ' + hi;
    return { q: 'Union-compatible R and S have ' + m + ' and ' + n + ' tuples. The number of tuples in ' + nm + ' can range from:', o: uniq4(ans, [Math.max(m, n) + ' to ' + (m + n), '0 to ' + Math.min(m, n), '0 to ' + m, Math.min(m, n) + ' to ' + Math.max(m, n), '0 to ' + (m + n)]), w: '∪: max(m,n) … m+n. ∩: 0 … min(m,n). R − S: 0 … |R|.' };
  } };
  G['db.index'] = { s: 'DBMS', t: 'Indexing', make: function (rng) {
    var r = R(rng);
    for (var t = 0; t < 100; t++) {
      var recs = r.pick([10000, 20000, 30000, 50000, 60000]), B = r.pick([512, 1024, 2048, 4096]), Rs = r.pick([100, 128, 150, 200, 250]), K = r.pick([5, 9, 10, 12]), P = r.pick([4, 6, 8]);
      var bf = Math.floor(B / Rs); if (bf < 2) continue; var blocks = Math.ceil(recs / bf), ibf = Math.floor(B / (K + P));
      var typ = r.pick(['none', 'primary', 'secondary']);
      var ans, w;
      if (typ === 'none') { ans = Math.ceil(Math.log2(blocks)); w = 'Blocking factor ⌊' + B + '/' + Rs + '⌋ = ' + bf + ', blocks = ⌈' + recs + '/' + bf + '⌉ = ' + blocks + '. Binary search: ⌈log₂ ' + blocks + '⌉ = ' + ans + '.'; }
      else { var entries = typ === 'primary' ? blocks : recs, ib = Math.ceil(entries / ibf); ans = Math.ceil(Math.log2(ib)) + 1; w = 'Data blocks = ' + blocks + ' (bf ' + bf + '). Index entry = ' + (K + P) + ' B → ' + ibf + ' per block. ' + (typ === 'primary' ? 'Primary index: one entry per block' : 'Secondary index: one entry per record') + ' → ' + entries + ' entries = ' + ib + ' index blocks. Accesses = ⌈log₂ ' + ib + '⌉ + 1 = ' + ans + '.'; }
      var o = uniq4(String(ans), [String(ans + 1), String(ans - 1), String(ans + 2), String(Math.ceil(Math.log2(blocks)))].filter(function (x) { return +x > 0; }));
      if (!o) continue;
      return { q: 'An ordered file has ' + recs + ' fixed-length records of ' + Rs + ' bytes, block size ' + B + ' bytes (unspanned), key ' + K + ' bytes, block pointer ' + P + ' bytes. How many block accesses to find a record by key ' + (typ === 'none' ? 'using binary search with no index' : 'using a single-level ' + typ + ' index') + '?', o: o, w: w };
    }
  } };
  G['db.border'] = { s: 'DBMS', t: 'Indexing', make: function (rng) {
    var r = R(rng), B = r.pick([512, 1024, 2048, 4096]), K = r.pick([8, 9, 10, 12, 16]), P = r.pick([4, 6, 8]), typ = r.pick(['bplus', 'btree']), Pr = r.pick([6, 7, 8]);
    var p;
    if (typ === 'bplus') { p = Math.floor((B + K) / (P + K)); }
    else { p = Math.floor((B + K + Pr) / (P + K + Pr)); }
    var q = typ === 'bplus' ? 'Block size ' + B + ' B, key ' + K + ' B, block pointer ' + P + ' B. Maximum order p (pointers) of a B+ tree INTERNAL node?' : 'Block size ' + B + ' B, key ' + K + ' B, tree pointer ' + P + ' B, record pointer ' + Pr + ' B. Maximum order p of a B-tree node?';
    var w = typ === 'bplus' ? 'p·P + (p − 1)·K ≤ B → p ≤ (B + K)/(P + K) = ' + p + '.' : 'p·P + (p − 1)(K + Pr) ≤ B → p ≤ (B + K + Pr)/(P + K + Pr) = ' + p + '.';
    return { q: q, o: uniq4(String(p), [String(p + 1), String(p - 1), String(Math.floor(B / (P + K))) === String(p) ? String(p + 2) : String(Math.floor(B / (P + K))), String(p - 2)]), w: w };
  } };
  G['db.agg'] = { s: 'DBMS', t: 'SQL', make: function (rng) {
    var r = R(rng);
    for (var t = 0; t < 100; t++) {
      var n = r.int(5, 7), vals = []; for (var i = 0; i < n; i++) vals.push(r.int(0, 3) === 0 ? null : r.int(1, 9) * 10);
      var nn = vals.filter(function (v) { return v !== null; }); if (nn.length < 2 || nn.length === n) continue;
      var sum = nn.reduce(function (a, b) { return a + b; }, 0), ask = r.pick(['countstar', 'countcol', 'avg', 'sumstar']);
      var ans, w, q = 'Column marks of table T has the values: ' + vals.map(function (v) { return v === null ? 'NULL' : v; }).join(', ') + '. ';
      if (ask === 'countstar') { q += 'SELECT COUNT(*) FROM T returns:'; ans = n; w = 'COUNT(*) counts rows, including those with NULL.'; }
      else if (ask === 'countcol') { q += 'SELECT COUNT(marks) FROM T returns:'; ans = nn.length; w = 'COUNT(column) skips NULLs.'; }
      else if (ask === 'avg') { q += 'SELECT AVG(marks) FROM T returns:'; ans = Math.round(sum / nn.length * 100) / 100; w = 'AVG ignores NULLs: ' + sum + ' / ' + nn.length + '.'; }
      else { q += 'SELECT SUM(marks)/COUNT(*) FROM T returns:'; ans = Math.round(sum / n * 100) / 100; w = 'SUM skips NULLs (' + sum + ') but COUNT(*) counts all ' + n + ' rows.'; }
      var c = [n, nn.length, Math.round(sum / nn.length * 100) / 100, Math.round(sum / n * 100) / 100, sum, n - nn.length].map(String);
      var o = uniq4(String(ans), r.shuffle(c)); if (!o) continue;
      return { q: q, o: o, w: w };
    }
  } };
  G['db.ertables'] = { s: 'DBMS', t: 'ER model', make: function (rng) {
    var r = R(rng), c = r.pick([['1:1', 'total on both sides', 1], ['1:1', 'partial on both sides', 2], ['1:N', 'any participation', 2], ['M:N', 'any participation', 3]]);
    return { q: 'Two strong entity sets E1 and E2 are linked by a binary relationship with cardinality ' + c[0] + ' and ' + c[1] + ' (no multivalued attributes). Minimum number of tables?', o: uniq4(String(c[2]), ['1', '2', '3', '4']), w: '1:1 with total participation on both sides → merge into 1 table. 1:N → 2 tables (FK on the N side). M:N → 3 tables (separate relationship table). 1:1 partial → 2 tables.' };
  } };
})(typeof window !== 'undefined' ? window : globalThis);
(function (root) {
  'use strict';
  var G = root.SnowGens.G;
  function R(rng) { return { int: function (a, b) { return a + Math.floor(rng() * (b - a + 1)); }, pick: function (a) { return a[Math.floor(rng() * a.length)]; }, shuffle: function (a) { a = a.slice(); for (var i = a.length - 1; i > 0; i--) { var j = Math.floor(rng() * (i + 1)); var t = a[i]; a[i] = a[j]; a[j] = t; } return a; } }; }
  function u4(c, cands) { var o = [String(c)]; function add(x) { x = String(x); if (o.length < 4 && o.indexOf(x) < 0 && !/NaN|undefined|Infinity/.test(x)) o.push(x); }
    cands.forEach(add);
    var cs = String(c), k;
    if (/^[01]+$/.test(cs)) { for (k = 0; k < cs.length && o.length < 4; k++) add(cs.slice(0, k) + (cs[k] === '0' ? '1' : '0') + cs.slice(k + 1)); }
    else if (/^-?[0-9.]+$/.test(cs)) { var v = parseFloat(cs), st = Math.abs(v) >= 10 ? Math.max(1, Math.round(Math.abs(v) * 0.1)) : 1; for (k = 1; o.length < 4 && k < 20; k++) add(Math.round((v + (k % 2 ? 1 : -1) * Math.ceil(k / 2) * st) * 100) / 100); }
    else if (/^\d+\.\d+\.\d+\.\d+$/.test(cs)) { var p = cs.split('.').map(Number); for (k = 1; o.length < 4 && k < 20; k++) { var q = p.slice(); q[3] = (q[3] + k * 16) % 256; add(q.join('.')); } }
    return o.length === 4 ? o : null; }
  function f2(x) { return String(Math.round(x * 100) / 100); }
  function ip(n) { return [n >>> 24, (n >>> 16) & 255, (n >>> 8) & 255, n & 255].join('.'); }
  function mask(p) { return p === 0 ? 0 : (0xFFFFFFFF << (32 - p)) >>> 0; }
  G['cn.hosts'] = { s: 'CN', t: 'IP addressing', make: function (rng) {
    var r = R(rng), p = r.int(16, 30), m = mask(p), h = Math.pow(2, 32 - p) - 2, as = r.pick(['mask', 'cidr']);
    return { q: 'A subnet has mask ' + (as === 'mask' ? ip(m) : '/' + p) + '. Maximum number of usable host addresses?', o: u4(h, [h + 2, h / 2 - 1, h * 2 + 2, Math.pow(2, 32 - p - 1)]), w: 'Host bits = 32 − ' + p + ' = ' + (32 - p) + '; hosts = 2^' + (32 - p) + ' − 2 = ' + h + ' (network and broadcast addresses excluded).' };
  } };
  G['cn.borrow'] = { s: 'CN', t: 'IP addressing', make: function (rng) {
    var r = R(rng), cls = r.pick([['C', 24], ['B', 16]]), ask = r.pick(['subnets', 'hosts']);
    if (ask === 'subnets') { var need = r.int(3, cls[0] === 'C' ? 30 : 500), b = Math.ceil(Math.log2(need)); if (cls[1] + b > 30) b = 30 - cls[1]; var p = cls[1] + b;
      return { q: 'A class ' + cls[0] + ' network must be split into at least ' + need + ' subnets, keeping as many hosts per subnet as possible. Which subnet mask?', o: u4(ip(mask(p)), [ip(mask(p + 1)), ip(mask(p - 1)), ip(mask(p + 2))]), w: 'Borrow ⌈log₂ ' + need + '⌉ = ' + b + ' bits → /' + p + ' = ' + ip(mask(p)) + '.' }; }
    var hn = r.int(5, cls[0] === 'C' ? 120 : 4000), hb = Math.ceil(Math.log2(hn + 2)), p2 = 32 - hb;
    return { q: 'In a class ' + cls[0] + ' network, each subnet needs at least ' + hn + ' hosts, and you want as many subnets as possible. Which mask?', o: u4(ip(mask(p2)), [ip(mask(p2 + 1)), ip(mask(p2 - 1)), ip(mask(p2 + 2))]), w: 'Need 2^h − 2 ≥ ' + hn + ' → h = ' + hb + ' host bits → /' + p2 + ' = ' + ip(mask(p2)) + ' (' + (Math.pow(2, hb) - 2) + ' hosts).' };
  } };
  G['cn.cidr'] = { s: 'CN', t: 'IP addressing', make: function (rng) {
    var r = R(rng), p = r.int(20, 29), a = ((r.int(11, 223) << 24) | (r.int(0, 255) << 16) | (r.int(0, 255) << 8) | r.int(1, 254)) >>> 0;
    var m = mask(p), first = (a & m) >>> 0, last = (first | (~m >>> 0)) >>> 0, ask = r.pick(['first', 'last', 'count']);
    if (ask === 'count') return { q: 'How many addresses are in the block ' + ip(a) + '/' + p + '?', o: u4(Math.pow(2, 32 - p), [Math.pow(2, 32 - p) - 2, Math.pow(2, p - 16 > 0 ? p - 16 : 1), Math.pow(2, 33 - p)]), w: 'N = 2^(32 − ' + p + ') = ' + Math.pow(2, 32 - p) + '.' };
    var ans = ask === 'first' ? ip(first) : ip(last), alt = ask === 'first' ? [ip(first + 1), ip(a), ip((a & mask(p - 1)) >>> 0), ip(last)] : [ip(last - 1), ip((last + 1) >>> 0), ip(first), ip((first | (~mask(p + 1) >>> 0)) >>> 0)];
    return { q: 'For the block containing ' + ip(a) + '/' + p + ', what is the ' + (ask === 'first' ? 'first (network) address' : 'last (broadcast) address') + '?', o: u4(ans, alt), w: 'Mask /' + p + ' = ' + ip(m) + '. First = address AND mask = ' + ip(first) + '; last = first with all host bits 1 = ' + ip(last) + '.' };
  } };
  G['cn.class'] = { s: 'CN', t: 'IP addressing', make: function (rng) {
    var r = R(rng), cls = r.pick(['A', 'B', 'C', 'D', 'E']), rg = { A: [1, 126], B: [128, 191], C: [192, 223], D: [224, 239], E: [240, 254] }[cls];
    var a = r.int(rg[0], rg[1]) + '.' + r.int(0, 255) + '.' + r.int(0, 255) + '.' + r.int(1, 254);
    var o = ['Class ' + cls]; ['A', 'B', 'C', 'D', 'E'].filter(function (x) { return x !== cls; }).forEach(function (x) { if (o.length < 4) o.push('Class ' + x); });
    return { q: 'The IP address ' + a + ' belongs to which class?', o: o, w: 'First octet: A 0–127, B 128–191, C 192–223, D 224–239 (multicast), E 240–255.' };
  } };
  G['cn.hamming'] = { s: 'CN', t: 'Error control', make: function (rng) {
    var r = R(rng), ask = r.pick(['dist', 'bits', 'dmin']);
    if (ask === 'dist') { var n = r.int(5, 8), x = r.int(0, (1 << n) - 1), y = r.int(0, (1 << n) - 1); if (x === y) y ^= 1; var b = function (v) { var s = v.toString(2); while (s.length < n) s = '0' + s; return s; }; var d = (x ^ y).toString(2).replace(/0/g, '').length;
      return { q: 'Hamming distance between ' + b(x) + ' and ' + b(y) + '?', o: u4(d, [d + 1, d - 1 > 0 ? d - 1 : d + 2, n - d === d ? d + 2 : n - d]), w: 'XOR = ' + b(x ^ y) + '; count the 1s = ' + d + '.' }; }
    if (ask === 'bits') { var m = r.int(4, 120), k = 1; while (Math.pow(2, k) < m + k + 1) k++;
      return { q: 'How many Hamming parity bits are needed for ' + m + ' data bits (single-error correction)?', o: u4(k, [k + 1, k - 1, Math.ceil(Math.log2(m))]), w: 'Smallest r with 2^r ≥ m + r + 1: 2^' + k + ' = ' + Math.pow(2, k) + ' ≥ ' + (m + k + 1) + '.' }; }
    var t = r.int(1, 6), mode = r.pick(['correct', 'detect']), ans = mode === 'correct' ? 2 * t + 1 : t + 1;
    return { q: 'Minimum Hamming distance needed to guarantee ' + (mode === 'correct' ? 'correction' : 'detection') + ' of up to ' + t + ' errors?', o: u4(ans, [mode === 'correct' ? t + 1 : 2 * t + 1, 2 * t, ans + 1]), w: 'Detect s errors: d ≥ s + 1. Correct t errors: d ≥ 2t + 1.' };
  } };
  G['cn.crc'] = { s: 'CN', t: 'Error control', make: function (rng) {
    var r = R(rng), gens = ['1011', '1101', '10011', '11001', '1001', '10101'], g = r.pick(gens), k = g.length - 1, dl = r.int(5, 8);
    var d = '1'; for (var i = 1; i < dl; i++) d += r.int(0, 1);
    var bits = (d + Array(k + 1).join('0')).split('').map(Number), gb = g.split('').map(Number);
    for (var j = 0; j <= bits.length - gb.length; j++) if (bits[j]) for (var t = 0; t < gb.length; t++) bits[j + t] ^= gb[t];
    var rem = bits.slice(-k).join('');
    function flip(s, i) { return s.slice(0, i) + (s[i] === '0' ? '1' : '0') + s.slice(i + 1); }
    return { q: 'Dataword ' + d + ', generator (divisor) ' + g + '. What CRC (remainder) is appended?', o: u4(rem, [flip(rem, 0), flip(rem, k - 1), rem.split('').reverse().join(''), flip(rem, Math.floor(k / 2))]), w: 'Append ' + k + ' zeros, divide by ' + g + ' using XOR (mod-2); remainder = ' + rem + '. Codeword = ' + d + rem + '.' };
  } };
  G['cn.capacity'] = { s: 'CN', t: 'Signals', make: function (rng) {
    var r = R(rng), ask = r.pick(['shannon', 'nyquist']);
    if (ask === 'shannon') { var B = r.pick([3, 4, 6, 8, 10, 20]) * 1000, snr = r.pick([3, 7, 15, 31, 63, 255]), C = B * Math.log2(1 + snr) / 1000;
      return { q: 'A channel has bandwidth ' + B / 1000 + ' kHz and SNR = ' + snr + ' (linear). Shannon capacity (kbps)?', o: u4(f2(C), [f2(2 * C), f2(B / 1000 * Math.log2(snr)), f2(C / 2)]), w: 'C = B log₂(1 + SNR) = ' + B / 1000 + ' × log₂' + (1 + snr) + ' = ' + f2(C) + ' kbps.' }; }
    var B2 = r.pick([3, 4, 6, 8, 20]) * 1000, L = r.pick([2, 4, 8, 16]), Cn = 2 * B2 * Math.log2(L) / 1000;
    return { q: 'Noiseless channel, bandwidth ' + B2 / 1000 + ' kHz, ' + L + ' signal levels. Maximum bit rate (kbps) by Nyquist?', o: u4(f2(Cn), [f2(Cn / 2), f2(B2 / 1000 * L), f2(Cn * 2)]), w: 'Bit rate = 2 × B × log₂ L = 2 × ' + B2 / 1000 + ' × ' + Math.log2(L) + ' = ' + f2(Cn) + ' kbps.' };
  } };
  G['cn.aloha'] = { s: 'CN', t: 'MAC', make: function (rng) {
    var r = R(rng), fb = r.pick([100, 200, 250, 500, 1000]), kbps = r.pick([100, 200, 250, 500, 1000]), tfr = fb / kbps; // ms
    var rate = r.pick([125, 250, 500, 1000]); while (rate * tfr / 1000 > 1.5) rate = rate / 2; var typ = r.pick(['pure', 'slotted']), G2 = rate * tfr / 1000;
    var S = typ === 'pure' ? G2 * Math.exp(-2 * G2) : G2 * Math.exp(-G2), fps = S * 1000 / tfr;
    return { q: typ[0].toUpperCase() + typ.slice(1) + ' ALOHA: ' + fb + '-bit frames on a ' + kbps + ' kbps channel; the system produces ' + rate + ' frames per second. About how many frames per second succeed?', o: u4(Math.round(fps), [Math.round(typ === 'pure' ? G2 * Math.exp(-G2) * 1000 / tfr : G2 * Math.exp(-2 * G2) * 1000 / tfr), Math.round(rate * 0.184), Math.round(rate * 0.368), Math.round(fps) + 10]), w: 'Tfr = ' + fb + '/' + kbps + ' kbps = ' + tfr + ' ms; G = ' + rate + ' × ' + tfr / 1000 + ' = ' + f2(G2) + '. S = G e^(' + (typ === 'pure' ? '−2G' : '−G') + ') = ' + f2(S) + ' → ' + Math.round(fps) + ' frames/s.' };
  } };
  G['cn.delay'] = { s: 'CN', t: 'Data link', make: function (rng) {
    var r = R(rng), L = r.pick([1000, 2000, 4000, 8000, 12000]), B = r.pick([1, 2, 4, 10]) * 1e6, dist = r.pick([200, 1000, 2000, 4000, 6000]) * 1000, v = 2e8, ask = r.pick(['total', 'eff', 'window']);
    var Tt = L / B * 1000, Tp = dist / v * 1000, a = Tp / Tt;
    if (ask === 'total') return { q: (/^8/.test(String(L)) ? 'An ' : 'A ') + L + '-bit frame is sent over a ' + B / 1e6 + ' Mbps link of length ' + dist / 1000 + ' km (propagation speed 2 × 10⁸ m/s). Time until the last bit reaches the receiver (ms)?', o: u4(f2(Tt + Tp), [f2(Tt), f2(Tp), f2(Tt + 2 * Tp)]), w: 'Tt = L/B = ' + f2(Tt) + ' ms; Tp = d/v = ' + f2(Tp) + ' ms; total = ' + f2(Tt + Tp) + ' ms.' };
    if (ask === 'eff') { var e = 1 / (1 + 2 * a) * 100; return { q: 'Stop-and-wait: ' + L + '-bit frames, ' + B / 1e6 + ' Mbps, ' + dist / 1000 + ' km link (2 × 10⁸ m/s). Link efficiency (%)?', o: u4(f2(e), [f2(1 / (1 + a) * 100), f2(Math.min(100, 2 * e)), f2(e / 2)]), w: 'a = Tp/Tt = ' + f2(Tp) + '/' + f2(Tt) + ' = ' + f2(a) + '; η = 1/(1 + 2a) = ' + f2(e) + '%.' }; }
    var W = Math.ceil(1 + 2 * a), bits = Math.ceil(Math.log2(W));
    return { q: 'Go-Back-N: ' + L + '-bit frames, ' + B / 1e6 + ' Mbps, ' + dist / 1000 + ' km link (2 × 10⁸ m/s). Minimum sequence-number bits for 100% utilisation?', o: u4(bits, [bits + 1, Math.max(1, bits - 1), bits + 2]), w: 'a = ' + f2(a) + '; window = ⌈1 + 2a⌉ = ' + W + '; bits = ⌈log₂ ' + W + '⌉ = ' + bits + '.' };
  } };
  G['cn.misc'] = { s: 'CN', t: 'Basics', make: function (rng) {
    var r = R(rng), ask = r.pick(['mesh', 'minframe', 'offset']);
    if (ask === 'mesh') { var n = r.int(4, 20), l = n * (n - 1) / 2; return { q: 'How many duplex links are needed for a full mesh of ' + n + ' devices, and how many ports per device?', o: u4(l + ' links, ' + (n - 1) + ' ports', [n * (n - 1) + ' links, ' + (n - 1) + ' ports', l + ' links, ' + n + ' ports', (n - 1) + ' links, ' + (n - 1) + ' ports']), w: 'n(n − 1)/2 = ' + l + '; each device connects to n − 1 = ' + (n - 1) + ' others.' }; }
    if (ask === 'minframe') { var B = r.pick([10, 100, 1000]) * 1e6, tp = r.pick([5, 10, 25.6, 50]) * 1e-6, Lm = 2 * tp * B; return { q: 'CSMA/CD at ' + B / 1e6 + ' Mbps with maximum propagation delay ' + Math.round(tp * 1e7) / 10 + ' µs. Minimum frame size (bits)?', o: u4(Math.round(Lm), [Math.round(Lm / 2), Math.round(Lm * 2), Math.round(Lm / 8)]), w: 'L_min = 2 × Tp × B = 2 × ' + Math.round(tp * 1e7) / 10 + ' µs × ' + B / 1e6 + ' Mbps = ' + Math.round(Lm) + ' bits.' }; }
    var sz = r.pick([1400, 1480, 2000, 800, 1200]), k = r.int(1, 4), off = sz * k / 8;
    return { q: 'A datagram is fragmented into pieces carrying ' + sz + ' data bytes each. What is the fragment-offset value of fragment number ' + (k + 1) + '?', o: u4(off, [sz * k, off + sz / 8, off / 2]), w: 'Offset counts 8-byte units: ' + sz * k + ' bytes / 8 = ' + off + '.' };
  } };
})(typeof window !== 'undefined' ? window : globalThis);
