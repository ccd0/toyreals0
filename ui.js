const $ = (s) => document.querySelector(s);
const input = $('textarea');
const button = $('button');
const inputDigits = $('input[type="number"]');
const output = $('output');
let result;

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
  const s = num.abs().toString().padStart(n + 1, '0');
  const i = s.length - n;
  return (num.lt(0) ? '-' : '') + s.substr(0, i) + '.' + s.substr(i);
}

function display() {
  if (result instanceof Array) {
    try {
      output.value = '\u2248 ' + to_digits(result, parseInt(inputDigits.value, 10));
    } catch(e) {
      output.value = e.toString();
    }
  } else {
    output.value = result.toString();
  }
}

button.addEventListener('click', compute);
input.addEventListener('keydown', (e) => {
  if (e.key === 'Enter') {
    compute();
    e.preventDefault();
  }
});
inputDigits.addEventListener('change', display);
