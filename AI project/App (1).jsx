import { useState, useCallback, useRef } from 'react'
import './index.css'

const ROWS = 21
const COLS = 45
const CELL = 22

const ROAD = 'empty'
const BLOCK = 'wall'
const START = 'start'
const END = 'end'
const VISITED = 'visited'
const PATH = 'path'

const COLORS = {
  empty: '#1e2535',
  wall: '#141b2d',
  start: '#22c55e',
  end: '#ef4444',
  visited: '#0e3a5a',
  path: '#facc15',
}

const ALGO_COLORS = {
  'A*':               { visited: '#1a3a5c', path: '#facc15', accent: '#facc15' },
  'Dijkstra':         { visited: '#1a3d2e', path: '#4ade80', accent: '#4ade80' },
  'BFS':              { visited: '#2a1f4a', path: '#a78bfa', accent: '#a78bfa' },
  'DFS':              { visited: '#3d1f1f', path: '#f87171', accent: '#f87171' },
  'Bidirectional BFS':{ visited: '#1a3040', path: '#38bdf8', accent: '#38bdf8' },
}

const ALL_ALGOS = ['A*', 'Dijkstra', 'BFS', 'DFS', 'Bidirectional BFS']

// ── Grid helpers ──────────────────────────────────────────────────────────────
const makeCityGrid = () =>
  Array.from({ length: ROWS }, (_, r) =>
    Array.from({ length: COLS }, (_, c) => ({
      r, c, type: (r % 4 === 0 || c % 4 === 0) ? ROAD : BLOCK
    }))
  )

const cloneGrid = (g) => g.map(row => row.map(cell => ({ ...cell })))

const getNeighbors = (grid, node) =>
  [[-1,0],[1,0],[0,-1],[0,1]]
    .map(([dr, dc]) => grid[node.r + dr]?.[node.c + dc])
    .filter(Boolean)

// ── Algorithms ────────────────────────────────────────────────────────────────
function aStar(grid, start, end) {
  const g = cloneGrid(grid)
  const s = g[start.r][start.c], e = g[end.r][end.c]
  const h = (a, b) => Math.abs(a.r - b.r) + Math.abs(a.c - b.c)
  s.g = 0; s.f = h(s, e)
  const open = [s], closed = new Set(), visited = []
  while (open.length) {
    open.sort((a, b) => a.f - b.f)
    const cur = open.shift()
    const key = `${cur.r},${cur.c}`
    if (closed.has(key)) continue
    closed.add(key); visited.push({ r: cur.r, c: cur.c })
    if (cur.r === e.r && cur.c === e.c) break
    for (const nb of getNeighbors(g, cur)) {
      if (nb.type === BLOCK || closed.has(`${nb.r},${nb.c}`)) continue
      const tg = (cur.g ?? Infinity) + 1
      if (tg < (nb.g ?? Infinity)) { nb.g = tg; nb.f = tg + h(nb, e); nb.parent = cur; open.push(nb) }
    }
  }
  return { visited, endNode: g[end.r][end.c] }
}

function dijkstra(grid, start, end) {
  const g = cloneGrid(grid)
  const s = g[start.r][start.c], e = g[end.r][end.c]
  s.dist = 0
  const open = [s], seen = new Set(), visited = []
  while (open.length) {
    open.sort((a, b) => (a.dist ?? Infinity) - (b.dist ?? Infinity))
    const cur = open.shift()
    const key = `${cur.r},${cur.c}`
    if (seen.has(key)) continue
    seen.add(key); visited.push({ r: cur.r, c: cur.c })
    if (cur.r === e.r && cur.c === e.c) break
    for (const nb of getNeighbors(g, cur)) {
      if (nb.type === BLOCK || seen.has(`${nb.r},${nb.c}`)) continue
      const d = (cur.dist ?? 0) + 1
      if (d < (nb.dist ?? Infinity)) { nb.dist = d; nb.parent = cur; open.push(nb) }
    }
  }
  return { visited, endNode: g[end.r][end.c] }
}

function bfs(grid, start, end) {
  const g = cloneGrid(grid)
  const s = g[start.r][start.c], e = g[end.r][end.c]
  const queue = [s], seen = new Set([`${s.r},${s.c}`]), visited = []
  while (queue.length) {
    const cur = queue.shift()
    visited.push({ r: cur.r, c: cur.c })
    if (cur.r === e.r && cur.c === e.c) break
    for (const nb of getNeighbors(g, cur)) {
      const key = `${nb.r},${nb.c}`
      if (nb.type === BLOCK || seen.has(key)) continue
      seen.add(key); nb.parent = cur; queue.push(nb)
    }
  }
  return { visited, endNode: g[end.r][end.c] }
}

function dfs(grid, start, end) {
  const g = cloneGrid(grid)
  const s = g[start.r][start.c], e = g[end.r][end.c]
  const stack = [s], seen = new Set([`${s.r},${s.c}`]), visited = []
  while (stack.length) {
    const cur = stack.pop()
    visited.push({ r: cur.r, c: cur.c })
    if (cur.r === e.r && cur.c === e.c) break
    for (const nb of getNeighbors(g, cur)) {
      const key = `${nb.r},${nb.c}`
      if (nb.type === BLOCK || seen.has(key)) continue
      seen.add(key); nb.parent = cur; stack.push(nb)
    }
  }
  return { visited, endNode: g[end.r][end.c] }
}

function bidirectionalBFS(grid, start, end) {
  const g = cloneGrid(grid)
  const s = g[start.r][start.c], e = g[end.r][end.c]
  const frontQ = [s], backQ = [e]
  const frontSeen = new Map([[`${s.r},${s.c}`, s]])
  const backSeen = new Map([[`${e.r},${e.c}`, e]])
  const visited = []
  let meetNode = null
  while (frontQ.length && backQ.length) {
    const fc = frontQ.shift()
    visited.push({ r: fc.r, c: fc.c })
    for (const nb of getNeighbors(g, fc)) {
      const key = `${nb.r},${nb.c}`
      if (nb.type === BLOCK || frontSeen.has(key)) continue
      nb.parentF = fc; frontSeen.set(key, nb); frontQ.push(nb)
      if (backSeen.has(key)) { meetNode = nb; break }
    }
    if (meetNode) break
    const bc = backQ.shift()
    visited.push({ r: bc.r, c: bc.c })
    for (const nb of getNeighbors(g, bc)) {
      const key = `${nb.r},${nb.c}`
      if (nb.type === BLOCK || backSeen.has(key)) continue
      nb.parentB = bc; backSeen.set(key, nb); backQ.push(nb)
      if (frontSeen.has(key)) { meetNode = frontSeen.get(key); break }
    }
    if (meetNode) break
  }
  const path = []
  if (meetNode) {
    let cur = meetNode
    const front = []
    while (cur) { front.unshift({ r: cur.r, c: cur.c }); cur = cur.parentF }
    cur = meetNode.parentB
    while (cur) { path.push({ r: cur.r, c: cur.c }); cur = cur.parentB }
    return { visited, path: [...front, ...path] }
  }
  return { visited, path: [] }
}

function getPath(endNode) {
  const path = []
  let cur = endNode
  while (cur) { path.unshift({ r: cur.r, c: cur.c }); cur = cur.parent }
  return path
}

const algoFns = {
  'A*': (g, s, e) => { const r = aStar(g, s, e); return { visited: r.visited, path: getPath(r.endNode) } },
  'Dijkstra': (g, s, e) => { const r = dijkstra(g, s, e); return { visited: r.visited, path: getPath(r.endNode) } },
  'BFS': (g, s, e) => { const r = bfs(g, s, e); return { visited: r.visited, path: getPath(r.endNode) } },
  'DFS': (g, s, e) => { const r = dfs(g, s, e); return { visited: r.visited, path: getPath(r.endNode) } },
  'Bidirectional BFS': (g, s, e) => bidirectionalBFS(g, s, e),
}

// ── Maze ──────────────────────────────────────────────────────────────────────
function generateMazeCells() {
  const walls = new Set()
  for (let r = 0; r < ROWS; r++)
    for (let c = 0; c < COLS; c++) walls.add(`${r},${c}`)
  const visited = new Set()
  const steps = []
  const carve = (r, c) => {
    visited.add(`${r},${c}`); walls.delete(`${r},${c}`)
    steps.push({ r, c, wall: false })
    const dirs = [[-2,0],[2,0],[0,-2],[0,2]].sort(() => Math.random() - 0.5)
    for (const [dr, dc] of dirs) {
      const nr = r + dr, nc = c + dc
      if (nr >= 0 && nr < ROWS && nc >= 0 && nc < COLS && !visited.has(`${nr},${nc}`)) {
        walls.delete(`${r+dr/2},${c+dc/2}`)
        steps.push({ r: r+dr/2, c: c+dc/2, wall: false })
        carve(nr, nc)
      }
    }
  }
  carve(1, 1)
  for (let r = 0; r < ROWS; r++)
    for (let c = 0; c < COLS; c++)
      if (walls.has(`${r},${c}`)) steps.push({ r, c, wall: true })
  return steps
}

const SPEEDS = { Slow: 60, Normal: 18, Fast: 4, Ludicrous: 1 }

const mkBtn = (active, color) => ({
  padding: '5px 13px', fontSize: '11px', letterSpacing: '1px',
  fontFamily: 'monospace', textTransform: 'uppercase', borderRadius: '4px',
  border: `1px solid ${active ? color : '#1e2a3a'}`,
  background: active ? color : 'transparent',
  color: active ? '#0a0e1a' : '#4a6a8a', cursor: 'pointer',
})

// ── Winner logic ──────────────────────────────────────────────────────────────
function pickWinner(results) {
  const valid = results.filter(r => r.path > 0)
  if (!valid.length) return null
  const minPath = Math.min(...valid.map(r => r.path))
  const shortest = valid.filter(r => r.path === minPath)
  // Among shortest, pick fewest explored
  shortest.sort((a, b) => a.explored - b.explored)
  return shortest[0].name
}

export default function App() {
  const [grid, setGrid] = useState(makeCityGrid)
  const [mode, setMode] = useState('start')
  const [speed, setSpeed] = useState('Normal')
  const [isDrawing, setIsDrawing] = useState(false)
  const [running, setRunning] = useState(false)
  const [comparing, setComparing] = useState(false)

  // Single mode
  const [singleAlgo, setSingleAlgo] = useState('A*')
  const [singleStats, setSingleStats] = useState(null)

  // Compare mode
  const [selectedAlgos, setSelectedAlgos] = useState(['A*', 'BFS'])
  const [compareResults, setCompareResults] = useState([])
  const [currentlyRunning, setCurrentlyRunning] = useState(null)

  const timeouts = useRef([])
  const clearTimeouts = () => { timeouts.current.forEach(clearTimeout); timeouts.current = [] }

  const clearViz = (g) => g.map(row => row.map(cell => ({
    ...cell, type: cell.type === VISITED || cell.type === PATH ? ROAD : cell.type
  })))

  const updateCell = useCallback((r, c) => {
    setGrid(prev => {
      const next = cloneGrid(prev)
      const cell = next[r][c]
      if (mode === 'block') {
        if (cell.type === START || cell.type === END) return prev
        cell.type = cell.type === BLOCK ? ROAD : BLOCK
      } else if (mode === 'start') {
        prev.flat().forEach(cl => { if (cl.type === START) next[cl.r][cl.c].type = ROAD })
        next[r][c].type = START
      } else if (mode === 'end') {
        prev.flat().forEach(cl => { if (cl.type === END) next[cl.r][cl.c].type = ROAD })
        next[r][c].type = END
      }
      return next
    })
  }, [mode])

  // ── Animate a single algorithm run ────────────────────────────────────────
  const animateRun = (visited, path, algoName, delay, onDone) => {
    const ac = ALGO_COLORS[algoName]
    visited.forEach((node, i) => {
      const t = setTimeout(() => {
        setGrid(prev => {
          const next = cloneGrid(prev)
          if (next[node.r][node.c].type === ROAD) next[node.r][node.c].type = VISITED
          return next
        })
      }, i * delay)
      timeouts.current.push(t)
    })
    path.forEach((node, i) => {
      const t = setTimeout(() => {
        setGrid(prev => {
          const next = cloneGrid(prev)
          if (next[node.r][node.c].type !== START && next[node.r][node.c].type !== END)
            next[node.r][node.c].type = PATH
          return next
        })
      }, visited.length * delay + i * delay * 2)
      timeouts.current.push(t)
    })
    const total = visited.length * delay + path.length * delay * 2
    const t = setTimeout(onDone, total + 100)
    timeouts.current.push(t)
  }

  // ── Single algorithm run ───────────────────────────────────────────────────
  const runSingle = () => {
    const start = grid.flat().find(c => c.type === START)
    const end = grid.flat().find(c => c.type === END)
    if (!start || !end) return alert('Place an origin and destination first!')
    if (running) return
    clearTimeouts()
    setRunning(true)
    setSingleStats(null)
    setCompareResults([])

    const clean = clearViz(grid)
    setGrid(clean)

    setTimeout(() => {
      const { visited, path } = algoFns[singleAlgo](clean, start, end)
      const delay = SPEEDS[speed]
      animateRun(visited, path, singleAlgo, delay, () => {
        setSingleStats({ explored: visited.length, path: path.length })
        setRunning(false)
      })
    }, 50)
  }

  // ── Compare: run algorithms one by one ────────────────────────────────────
  const runCompare = () => {
    const start = grid.flat().find(c => c.type === START)
    const end = grid.flat().find(c => c.type === END)
    if (!start || !end) return alert('Place an origin and destination first!')
    if (selectedAlgos.length < 2) return alert('Select at least 2 algorithms to compare!')
    if (running) return

    clearTimeouts()
    setRunning(true)
    setCompareResults([])
    setSingleStats(null)

    const baseGrid = clearViz(grid)
    setGrid(baseGrid)

    const results = []
    const delay = SPEEDS[speed]

    const runNext = (index) => {
      if (index >= selectedAlgos.length) {
        setCurrentlyRunning(null)
        setRunning(false)
        setCompareResults(results)
        return
      }

      const algoName = selectedAlgos[index]
      setCurrentlyRunning(algoName)

      // Clear previous visualization but keep walls + start/end
      setGrid(prev => clearViz(prev))

      setTimeout(() => {
        const freshGrid = clearViz(baseGrid)
        const { visited, path } = algoFns[algoName](freshGrid, start, end)

        results.push({ name: algoName, explored: visited.length, path: path.length })

        animateRun(visited, path, algoName, delay, () => {
          runNext(index + 1)
        })
      }, 300)
    }

    runNext(0)
  }

  const resetGrid = () => { clearTimeouts(); setRunning(false); setSingleStats(null); setCompareResults([]); setCurrentlyRunning(null); setGrid(makeCityGrid()) }
  const clearRoute = () => { clearTimeouts(); setRunning(false); setSingleStats(null); setCompareResults([]); setCurrentlyRunning(null); setGrid(prev => clearViz(prev)) }

  const runMaze = () => {
    clearTimeouts(); setRunning(true); setSingleStats(null); setCompareResults([])
    setGrid(makeCityGrid())
    const steps = generateMazeCells()
    steps.forEach((step, i) => {
      const t = setTimeout(() => {
        setGrid(prev => { const next = cloneGrid(prev); next[step.r][step.c].type = step.wall ? BLOCK : ROAD; return next })
        if (i === steps.length - 1) {
          setGrid(prev => { const next = cloneGrid(prev); steps.forEach(s => { if (s.wall) next[s.r][s.c].type = BLOCK }); return next })
          setRunning(false)
        }
      }, i * 8)
      timeouts.current.push(t)
    })
  }

  const toggleAlgo = (name) => {
    setSelectedAlgos(prev =>
      prev.includes(name) ? prev.filter(a => a !== name) : [...prev, name]
    )
  }

  const winner = compareResults.length ? pickWinner(compareResults) : null
  const modeAccent = { start: '#22c55e', end: '#ef4444', block: '#4a6a8a' }

  return (
    <div style={{ minHeight: '100vh', background: '#0a0e1a', display: 'flex', flexDirection: 'column', alignItems: 'center', padding: '1rem' }}>

      {/* Header */}
      <div style={{ marginBottom: '0.8rem', textAlign: 'center' }}>
        <div style={{ display: 'flex', alignItems: 'center', gap: '8px', justifyContent: 'center' }}>
          <svg width="16" height="16" viewBox="0 0 24 24" fill="none">
            <circle cx="12" cy="10" r="3" stroke="#facc15" strokeWidth="2"/>
            <path d="M12 2C7.58 2 4 5.58 4 10c0 6 8 13 8 13s8-7 8-13c0-4.42-3.58-8-8-8z" stroke="#facc15" strokeWidth="1.5" fill="rgba(250,204,21,0.08)"/>
          </svg>
          <span style={{ fontSize: '13px', letterSpacing: '6px', color: '#94a3b8', fontWeight: 400, fontFamily: 'monospace' }}>CITY PATHFINDER</span>
        </div>
        <p style={{ fontSize: '10px', color: '#1e3050', marginTop: '3px', letterSpacing: '2px', fontFamily: 'monospace' }}>AI ROUTE VISUALIZER + ALGORITHM COMPARISON</p>
      </div>

      {/* Main toolbar */}
      <div style={{ display: 'flex', flexWrap: 'wrap', gap: '6px', justifyContent: 'center', marginBottom: '0.6rem', background: '#0d1420', border: '1px solid #1a2535', borderRadius: '8px', padding: '8px 12px' }}>

        {/* Draw mode */}
        <div style={{ display: 'flex', gap: '4px' }}>
          {[['start','Origin'],['end','Destination'],['block','Block']].map(([m, label]) => (
            <button key={m} onClick={() => setMode(m)} style={mkBtn(mode === m, modeAccent[m])}>{label}</button>
          ))}
        </div>

        <div style={{ width: '1px', background: '#1a2535', margin: '0 2px' }} />

        {/* Speed */}
        <select value={speed} onChange={e => setSpeed(e.target.value)} style={{ background: '#0d1420', color: '#4a6a8a', border: '1px solid #1e2a3a', padding: '5px 8px', fontSize: '11px', fontFamily: 'monospace', borderRadius: '4px' }}>
          {Object.keys(SPEEDS).map(s => <option key={s}>{s}</option>)}
        </select>

        <div style={{ width: '1px', background: '#1a2535', margin: '0 2px' }} />

        <button onClick={clearRoute} disabled={running} style={mkBtn(false, '#4a6a8a')}>Clear</button>
        <button onClick={runMaze} disabled={running} style={mkBtn(false, '#4a6a8a')}>Gen City</button>
        <button onClick={resetGrid} disabled={running} style={mkBtn(false, '#4a6a8a')}>Reset</button>
      </div>

      {/* Two panels: Single + Compare */}
      <div style={{ display: 'flex', gap: '10px', marginBottom: '0.6rem', flexWrap: 'wrap', justifyContent: 'center' }}>

        {/* ── Single Run Panel ── */}
        <div style={{ background: '#0d1420', border: '1px solid #1a2535', borderRadius: '8px', padding: '10px 14px', minWidth: '220px' }}>
          <div style={{ fontSize: '10px', color: '#2d4a6a', letterSpacing: '2px', fontFamily: 'monospace', marginBottom: '8px' }}>SINGLE RUN</div>
          <div style={{ display: 'flex', gap: '6px', alignItems: 'center' }}>
            <select value={singleAlgo} onChange={e => setSingleAlgo(e.target.value)} style={{ background: '#0a0e1a', color: '#8899aa', border: '1px solid #1e2a3a', padding: '5px 8px', fontSize: '11px', fontFamily: 'monospace', borderRadius: '4px', flex: 1 }}>
              {ALL_ALGOS.map(a => <option key={a}>{a}</option>)}
            </select>
            <button onClick={runSingle} disabled={running} style={{ padding: '5px 14px', fontSize: '11px', letterSpacing: '1px', fontFamily: 'monospace', textTransform: 'uppercase', background: running ? '#0d1a2d' : '#854d0e', color: running ? '#2a4060' : '#facc15', border: `1px solid ${running ? '#1a2a40' : '#a16207'}`, borderRadius: '4px', cursor: running ? 'default' : 'pointer', whiteSpace: 'nowrap' }}>
              {running && !comparing ? '...' : '▶ Run'}
            </button>
          </div>
          {singleStats && (
            <div style={{ marginTop: '8px', fontSize: '11px', fontFamily: 'monospace', color: '#4a6a8a' }}>
              <span>Explored <span style={{ color: '#0ea5e9' }}>{singleStats.explored}</span></span>
              <span style={{ margin: '0 8px', color: '#1a2535' }}>|</span>
              <span>Route <span style={{ color: '#facc15' }}>{singleStats.path > 0 ? singleStats.path : 'none'}</span></span>
            </div>
          )}
        </div>

        {/* ── Compare Panel ── */}
        <div style={{ background: '#0d1420', border: '1px solid #1a2535', borderRadius: '8px', padding: '10px 14px', minWidth: '340px' }}>
          <div style={{ fontSize: '10px', color: '#2d4a6a', letterSpacing: '2px', fontFamily: 'monospace', marginBottom: '8px' }}>COMPARE MODE — pick algorithms</div>

          {/* Checkboxes */}
          <div style={{ display: 'flex', flexWrap: 'wrap', gap: '6px', marginBottom: '8px' }}>
            {ALL_ALGOS.map(name => {
              const checked = selectedAlgos.includes(name)
              const ac = ALGO_COLORS[name]
              return (
                <label key={name} style={{ display: 'flex', alignItems: 'center', gap: '5px', cursor: 'pointer', fontSize: '11px', fontFamily: 'monospace', padding: '4px 10px', borderRadius: '4px', border: `1px solid ${checked ? ac.accent : '#1e2a3a'}`, background: checked ? `${ac.accent}18` : 'transparent', color: checked ? ac.accent : '#4a6a8a', userSelect: 'none' }}>
                  <input type="checkbox" checked={checked} onChange={() => toggleAlgo(name)} style={{ accentColor: ac.accent, width: 12, height: 12 }} />
                  {name}
                </label>
              )
            })}
          </div>

          <div style={{ display: 'flex', alignItems: 'center', gap: '8px' }}>
            <button
              onClick={runCompare}
              disabled={running || selectedAlgos.length < 2}
              style={{ padding: '5px 16px', fontSize: '11px', letterSpacing: '1px', fontFamily: 'monospace', textTransform: 'uppercase', background: running ? '#0d1a2d' : selectedAlgos.length < 2 ? '#111' : '#1d3a6a', color: running ? '#2a4060' : selectedAlgos.length < 2 ? '#2a3a50' : '#60a5fa', border: `1px solid ${running || selectedAlgos.length < 2 ? '#1a2a40' : '#2563eb'}`, borderRadius: '4px', cursor: running || selectedAlgos.length < 2 ? 'default' : 'pointer' }}
            >
              {running ? `● Running ${currentlyRunning || ''}...` : '▶▶ Compare'}
            </button>
            {currentlyRunning && (
              <span style={{ fontSize: '10px', fontFamily: 'monospace', color: ALGO_COLORS[currentlyRunning]?.accent }}>
                {currentlyRunning}
              </span>
            )}
          </div>
        </div>
      </div>

      {/* Results table */}
      {compareResults.length > 0 && (
        <div style={{ marginBottom: '0.6rem', background: '#0d1420', border: '1px solid #1a2535', borderRadius: '8px', padding: '10px 14px', minWidth: '400px' }}>
          <div style={{ fontSize: '10px', color: '#2d4a6a', letterSpacing: '2px', fontFamily: 'monospace', marginBottom: '8px' }}>RESULTS</div>
          <table style={{ width: '100%', borderCollapse: 'collapse', fontFamily: 'monospace', fontSize: '12px' }}>
            <thead>
              <tr>
                {['Algorithm', 'Roads Explored', 'Route Length', 'Verdict'].map(h => (
                  <th key={h} style={{ textAlign: 'left', padding: '6px 10px', color: '#2d4a6a', fontWeight: 400, fontSize: '10px', letterSpacing: '1px', borderBottom: '1px solid #1a2535' }}>{h.toUpperCase()}</th>
                ))}
              </tr>
            </thead>
            <tbody>
              {compareResults
                .slice()
                .sort((a, b) => {
                  if (a.path === 0 && b.path > 0) return 1
                  if (b.path === 0 && a.path > 0) return -1
                  if (a.path !== b.path) return a.path - b.path
                  return a.explored - b.explored
                })
                .map((r, i) => {
                  const isWinner = r.name === winner
                  const ac = ALGO_COLORS[r.name]
                  return (
                    <tr key={r.name} style={{ background: isWinner ? `${ac.accent}12` : 'transparent' }}>
                      <td style={{ padding: '7px 10px', color: ac.accent, borderBottom: '1px solid #111827' }}>
                        {isWinner && <span style={{ marginRight: 6 }}>★</span>}{r.name}
                      </td>
                      <td style={{ padding: '7px 10px', color: '#4a6a8a', borderBottom: '1px solid #111827' }}>{r.explored}</td>
                      <td style={{ padding: '7px 10px', color: r.path > 0 ? '#94a3b8' : '#ef4444', borderBottom: '1px solid #111827' }}>
                        {r.path > 0 ? `${r.path} blocks` : 'Not found'}
                      </td>
                      <td style={{ padding: '7px 10px', borderBottom: '1px solid #111827' }}>
                        {isWinner
                          ? <span style={{ color: ac.accent, fontSize: '11px' }}>BEST ROUTE</span>
                          : r.path === 0
                            ? <span style={{ color: '#ef4444', fontSize: '11px' }}>NO PATH</span>
                            : <span style={{ color: '#2d4a6a', fontSize: '11px' }}>—</span>
                        }
                      </td>
                    </tr>
                  )
                })}
            </tbody>
          </table>
          {winner && (
            <div style={{ marginTop: '10px', padding: '8px 12px', background: `${ALGO_COLORS[winner]?.accent}15`, border: `1px solid ${ALGO_COLORS[winner]?.accent}40`, borderRadius: '6px', fontSize: '11px', fontFamily: 'monospace', color: ALGO_COLORS[winner]?.accent }}>
              ★ {winner} wins — shortest route with fewest roads explored
            </div>
          )}
        </div>
      )}

      {/* Grid */}
      <div style={{ borderRadius: '6px', overflow: 'hidden', border: '1px solid #1a2535' }}>
        <div
          style={{ display: 'grid', gridTemplateColumns: `repeat(${COLS}, ${CELL}px)`, gap: '1px', background: '#0d1420', cursor: 'crosshair' }}
          onMouseLeave={() => setIsDrawing(false)}
        >
          {grid.flat().map(({ r, c, type }) => (
            <div
              key={`${r}-${c}`}
              style={{
                width: CELL, height: CELL,
                background: COLORS[type],
                position: 'relative',
                transition: type === VISITED ? 'background 0.2s' : 'none',
                border: type === BLOCK ? '1px solid #0d1420' : 'none',
                boxSizing: 'border-box',
              }}
              onMouseDown={() => { if (!running) { setIsDrawing(true); updateCell(r, c) } }}
              onMouseEnter={() => { if (!running && isDrawing && mode === 'block') updateCell(r, c) }}
              onMouseUp={() => setIsDrawing(false)}
            >
              {type === START && (
                <div style={{ position: 'absolute', inset: 0, display: 'flex', alignItems: 'center', justifyContent: 'center' }}>
                  <div style={{ width: 10, height: 10, borderRadius: '50%', background: '#22c55e', border: '2px solid #fff', boxShadow: '0 0 8px rgba(34,197,94,0.9)' }} />
                </div>
              )}
              {type === END && (
                <div style={{ position: 'absolute', inset: 0, display: 'flex', alignItems: 'center', justifyContent: 'center' }}>
                  <div style={{ width: 10, height: 10, borderRadius: '50%', background: '#ef4444', border: '2px solid #fff', boxShadow: '0 0 8px rgba(239,68,68,0.9)' }} />
                </div>
              )}
            </div>
          ))}
        </div>
      </div>

      {/* Legend */}
      <div style={{ display: 'flex', gap: '1rem', marginTop: '0.7rem', fontSize: '10px', fontFamily: 'monospace', color: '#1e3050', flexWrap: 'wrap', justifyContent: 'center', letterSpacing: '1px' }}>
        {[
          { color: '#22c55e', label: 'ORIGIN' },
          { color: '#ef4444', label: 'DEST' },
          { color: '#141b2d', label: 'BLOCK' },
          { color: '#0e3a5a', label: 'EXPLORED' },
          { color: '#facc15', label: 'ROUTE' },
        ].map(({ color, label }) => (
          <span key={label} style={{ display: 'flex', alignItems: 'center', gap: '4px' }}>
            <span style={{ width: 9, height: 9, background: color, display: 'inline-block', borderRadius: '2px' }} />
            {label}
          </span>
        ))}
        <span style={{ color: '#1e3050' }}>|</span>
        {ALL_ALGOS.map(name => (
          <span key={name} style={{ display: 'flex', alignItems: 'center', gap: '4px' }}>
            <span style={{ width: 9, height: 9, background: ALGO_COLORS[name].path, display: 'inline-block', borderRadius: '2px' }} />
            <span style={{ color: ALGO_COLORS[name].accent }}>{name}</span>
          </span>
        ))}
      </div>

    </div>
  )
}
