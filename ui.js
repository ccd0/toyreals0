const $ = (s) => document.querySelector(s);
const input = $('textarea');
const button = $('button');
const inputDigits = $('input[type="number"]');
const output = $('output');
var result;

function compute() {
  try {
    result = Parser.evaluate(input.value);
  } catch(e) {
    result = e;
  }
  display();
}

function to_digits(x, n) {
  const exp = R.Z2R(bigInt(10).pow(n));
  const num = bigInt(R.round(R.mult(x, exp)));
  const s1 = num.abs().toString();
  const s = Array(Math.max(n + 1 - s1.length, 0) + 1).join('0') + s1;
  const i = s.length - n;
  return (num.lt(0) ? '-' : '') + s.substr(0, i) + '.' + s.substr(i);
}

function display() {
  try {
    const n_digits = parseInt(inputDigits.value, 10);
    if (result && result.t === 'R') {
      output.value = '\u2248 ' + to_digits(result, n_digits);
    } else if (result && result.t === 'RI') {
      output.value = 'min \u2248 ' + to_digits(result.min, n_digits) + '\nmax \u2248 ' + to_digits(result.max, n_digits);
    } else if (typeof result === 'function') {
      output.value = '[function]';
    } else if (typeof result === 'undefined') {
      output.value = '';
    } else {
      output.value = String(result);
    }
  } catch(e) {
    output.value = String(e);
  }
}

button.addEventListener('click', compute);
input.addEventListener('keydown', (e) => {
  if (e.key === 'Enter' && !e.shiftKey) {
    e.preventDefault();
    compute();
  }
});
inputDigits.addEventListener('change', display);
