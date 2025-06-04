// script.js

function $(id) {
  return document.getElementById(id);
}

const nInput = $("n-input");
const kInput = $("k-input");
const generateBtn = $("generate-btn");
const gameInputArea = $("game-input-area");
const computeArea = $("compute-area");
const resultDiv = $("result");

generateBtn.addEventListener("click", () => {
  const n = parseInt(nInput.value);
  const k = parseInt(kInput.value);

  gameInputArea.innerHTML = "";
  resultDiv.innerHTML = "";
  computeArea.style.display = "none";

  const tbl = document.createElement("table");
  const thead = document.createElement("thead");
  const headerRow = document.createElement("tr");

  const emptyTh = document.createElement("th");
  emptyTh.textContent = "";
  headerRow.appendChild(emptyTh);

  // create columns
  for (let j = 0; j < k; j++) {
    const th = document.createElement("th");
    th.textContent = `Game ${j + 1}`;
    headerRow.appendChild(th);
  }
  thead.appendChild(headerRow);

  const quotaRow = document.createElement("tr");
  const quotaLabel = document.createElement("td");
  quotaLabel.textContent = "Quota";
  quotaLabel.classList.add("small");
  quotaRow.appendChild(quotaLabel);

  for (let j = 0; j < k; j++) {
    const td = document.createElement("td");
    const inp = document.createElement("input");
    inp.type = "number";
    inp.min = "0";
    inp.value = "0";
    inp.id = `quota-${j}`;
    td.appendChild(inp);
    quotaRow.appendChild(td);
  }
  thead.appendChild(quotaRow);

  // create rows
  const tbody = document.createElement("tbody");
  for (let i = 0; i < n; i++) {
    const row = document.createElement("tr");
    const labelTd = document.createElement("td");
    labelTd.textContent = `Player ${i + 1}`;
    labelTd.classList.add("small");
    row.appendChild(labelTd);

    for (let j = 0; j < k; j++) {
      const td = document.createElement("td");
      const inp = document.createElement("input");
      inp.type = "number";
      inp.min = "0";
      inp.value = "0";
      inp.id = `weight-${i}-${j}`;
      td.appendChild(inp);
      row.appendChild(td);
    }
    tbody.appendChild(row);
  }

  tbl.appendChild(thead);
  tbl.appendChild(tbody);
  gameInputArea.appendChild(tbl);

  computeArea.style.display = "block";
});

$("compute-btn").addEventListener("click", () => {
  resultDiv.innerHTML = "";

  const n = parseInt(nInput.value);
  const k = parseInt(kInput.value);

  // get quotas
  const quotas = [];
  for (let j = 0; j < k; j++) {
    const q = parseInt($(`quota-${j}`).value, 10);
    quotas.push(q);
  }

  // get weights
  const weights = [];
  for (let i = 0; i < n; i++) {
    const row = [];
    for (let j = 0; j < k; j++) {
      const w = parseInt($(`weight-${i}-${j}`).value, 10);
      row.push(w);
    }
    weights.push(row);
  }

  // get choice
  const choice = document.querySelector(
    'input[name="index-choice"]:checked'
  ).value;

  // return values
  if (choice === "shapley") {
    const shapleyVals = computeShapley(n, k, weights, quotas);
    displayShapley(shapleyVals);
  } else {
    const { raw, normalized } = computeBanzhaf(n, k, weights, quotas);
    displayBanzhaf(raw, normalized);
  }
});

// check if a coalition wins - all quotas met
function coalitionWins(coalitionMask, n, k, weights, quotas) {
  const sumWeights = Array(k).fill(0);
  for (let i = 0; i < n; i++) {
    if ((coalitionMask & (1 << i)) !== 0) {
      for (let j = 0; j < k; j++) {
        sumWeights[j] += weights[i][j];
      }
    }
  }
  for (let j = 0; j < k; j++) {
    if (sumWeights[j] < quotas[j]) {
      return false;
    }
  }
  return true;
}

// banzhaf index
// probability that player i is pivotal in coalition S
function computeBanzhaf(n, k, weights, quotas) {
  const rawCount = Array(n).fill(0);
  const totalSubsets = 1 << n;

  for (let mask = 0; mask < totalSubsets; mask++) {
    const S_wins = coalitionWins(mask, n, k, weights, quotas);

    for (let i = 0; i < n; i++) {
      const bit = 1 << i;
      if ((mask & bit) === 0) { // i is not in coalition S
        if (!S_wins && coalitionWins(mask | bit, n, k, weights, quotas)) {
          rawCount[i]++;
        }
      }
    }
  }

  const totalRaw = rawCount.reduce((a, b) => a + b, 0);
  const normalizedCount = rawCount.map(count => (count / Math.pow(2, n-1)).toFixed(6));
  
  return {
    raw: normalizedCount
  };
}

// shapley value
// %coalitions where S is losing, but S ∪ {i} is winning
function computeShapley(n, k, weights, quotas) {
  const counts = Array(n).fill(0);
  const used = Array(n).fill(false);
  const usedWeights = Array(k).fill(0);

  let totalPermutations = 0;

  function dfs(depth) {
    if (depth === n) {
      totalPermutations++;
      return;
    }

    // add next player
    for (let i = 0; i < n; i++) {
      if (used[i]) continue;

      // get new weight
      const newWeights = usedWeights.slice(); // shallow copy
      for (let j = 0; j < k; j++) {
        newWeights[j] += weights[i][j];
      }

      // check if i is pivotal
      const wasLosing = !arrayMeetsQuotas(usedWeights, quotas);
      const becomesWinning = arrayMeetsQuotas(newWeights, quotas);

      if (wasLosing && becomesWinning) {
        const suffixFactorial = factorial(n - depth - 1);
        counts[i] += suffixFactorial;
        totalPermutations += suffixFactorial;
      } else {
        used[i] = true;
        const oldWeights = usedWeights.slice();
        for (let j = 0; j < k; j++) {
          usedWeights[j] = newWeights[j];
        }
        dfs(depth + 1);
        used[i] = false;
        for (let j = 0; j < k; j++) {
          usedWeights[j] = oldWeights[j];
        }
      }
    }
  }

  dfs(0);

  // Finally, Shapley value = counts[i] / n!
  const nFactorial = factorial(n);
  return counts.map((c) => ((c / nFactorial).toFixed(6)));
}

// check if an players meets all quotas
function arrayMeetsQuotas(sums, quotas) {
  for (let j = 0; j < quotas.length; j++) {
    if (sums[j] < quotas[j]) {
      return false;
    }
  }
  return true;
}

// get factorial using DP
const factMemo = {};
function factorial(x) {
  if (x <= 1) return 1;
  if (factMemo[x]) return factMemo[x];
  return (factMemo[x] = x * factorial(x - 1));
}

// display results
function displayShapley(shapleyVals) {
  const n = shapleyVals.length;
  let html = `<h2>Shapley Values </h2>\n`;
  html += `<table>`;
  html += `<tr><th>Player</th><th>Shapley Value</th></tr>`;
  for (let i = 0; i < n; i++) {
    html += `<tr><td>Player ${i + 1}</td><td>${shapleyVals[i]}</td></tr>`;
  }
  html += `</table>`;
  resultDiv.innerHTML = html;
}
function displayBanzhaf(raw, normalized) {
  const n = raw.length;
  let html = `<h2>Banzhaf Indices</h2>\n`;
  html += `<table>`;
  html += `<tr><th>Player</th><th>Raw Banzhaf</th></tr>`;
  for (let i = 0; i < n; i++) {
    html += `<tr><td>Player ${i + 1}</td><td>${raw[i]}</td></tr>`;
  }
  html += `</table>`;
  resultDiv.innerHTML = html;
}
