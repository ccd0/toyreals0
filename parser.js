const Parser = (function() {

function tokenize(expr) {
  return expr.match(/[a-z_]\w*|[\d\.]+|[<=>]+|\S/gi) || [];
}

function table(values) {
  return Map.prototype.get.bind(new Map(Object.entries(values)));
}

const prefix = table({
  '(': ['paren', [0, ')']],
  '[': ['interval', [0, ',', 0, ']']],
  '/': ['inv', [70]],
  '-': ['opp', [70]]
});

const infix = table({
  '*': ['mult', [61], 60],
  '/': ['div', [61], 60],
  '+': ['plus', [51], 50],
  '-': ['minus', [51], 50],
  '=>': ['lambda', [10], 10]
});

function is_nullary(token) {
  return /^\w/i.test(token);
}

function repeat(str, n) {
  return new Array(n+1).join(str);
}

function parse_nullary(token) {
  if (/^\d/.test(token)) {
    if (/\./.test(token)) {
      const parts = token.split('.');
      if (parts.length !== 2 || token.length === 1) throw 'parse error';
      const num = parts[0] + parts[1];
      const den = '1' + repeat('0', parts[1].length);
      return ['div', ['num', num], ['num', den]];
    } else {
      return ['num', token];
    }
  } else {
    return ['id', token];
  }
}

function parse(tokens) {
  const [result, i] = parse_sub(tokens, 0, 0);
  if (i !== tokens.length) throw 'parse error';
  return result;
}

function parse_sub(tokens, start, level) {
  if (start >= tokens.length) throw 'parse error';
  let i = start;
  let token = tokens[i];
  let result, op;
  if (is_nullary(token)) {
    result = parse_nullary(token);
    i++;
  } else if ((op = prefix(token))) {
    [result, i] = parse_op(op, tokens, i);
  } else {
    throw 'parse error';
  }
  while (i < tokens.length) {
    token = tokens[i];
    if (is_nullary(token)) {
      result = ['apply', result, parse_nullary(token)];
      i++;
    } else if ((op = infix(token))) {
      if (op[2] >= level) {
        let lhs = result;
        if (op[0] === 'lambda') {
          if (lhs[0] !== 'id') throw 'parse error';
          lhs = lhs[1];
        }
        [result, i] = parse_op(op, tokens, i);
        result.splice(1, 0, lhs);
      } else {
        return [result, i];
      }
    } else if ((op = prefix(token))) {
      let arg;
      [arg, i] = parse_op(op, tokens, i);
      result = ['apply', result, arg];
    } else {
      return [result, i];
    }
  }
  return [result, i];
}

function parse_op(op, tokens, start) {
  const [name, parts] = op;
  let result = [name];
  let i = start + 1;
  let arg;
  for (let part of parts) {
    if (typeof part === 'number') {
      [arg, i] = parse_sub(tokens, i, part);
      result.push(arg);
    } else {
      if (tokens[i++] !== part) throw 'parse error';
    }
  }
  if (name === 'paren') result = result[1];
  return [result, i];
}

function AR(x, context) {
  if (!x || x.t !== 'R') throw 'type error';
  return x;
}

function ARI(x, context) {
  if (!x || x.t !== 'RI') throw 'type error';
  return x;
}

function AF(x) {
  if (typeof x !== 'function') throw 'type error';
  return x;
}

function R2Z(x, context) {
  const x0 = R.nth(AR(x), 0);
  if (x0.min.den !== 1 || x0.max.den !== 1 || x0.min.num !== x0.max.num) {
    throw 'type error';
  }
  return x0.min.num;
}

const operations = table({
  num: (x) => R.Z2R(bigInt(x)),
  apply: (f, x) => AF(f)(x),
  interval: (x, y) => ({t: 'RI', min: AR(x), max: AR(y)}),
  inv: (x) => R.inv(AR(x)),
  opp: (x) => R.opp(AR(x)),
  mult: (x, y) => R.mult(AR(x), AR(y)),
  div: (x, y) => R.div(AR(x), AR(y)),
  plus: (x, y) => R.plus(AR(x), AR(y)),
  minus: (x, y) => R.minus(AR(x), AR(y))
});

const constants = table({
  min: (xs) => ARI(xs).min,
  max: (xs) => ARI(xs).max,
  intersect: (f) => R.nested_RI_int((i) => ARI(f(R.Z2R(i)))),
  repeat: (n) => (f) => (x) => {
    n = R2Z(n);
    AF(f);
    for (let i = bigInt.zero; i.lt(n); i = i.add(1)) {
      x = f(x);
    }
    return x;
  }
});

function extend(table_fun, key, val) {
  return (key2) => (key2 === key) ? val : table_fun(key2);
}

function evaluate_ast(ast, environment=constants) {
  if (ast[0] === 'id') {
    const id = environment(ast[1]);
    if (!id) throw `undefined identifier "${ast[1]}"`;
    return id;
  } else if (ast[0] === 'lambda') {
    return (x) => evaluate_ast(ast[2], extend(environment, ast[1], x));
  } else {
    const args = ast.slice(1).map(x =>
      (typeof x === 'string') ? x : evaluate_ast(x, environment)
    );
    return operations(ast[0]).apply(this, args);
  }
}

function evaluate(expr) {
  return evaluate_ast(parse(tokenize(expr)));
}

return {tokenize, parse, evaluate_ast, evaluate};

})();
