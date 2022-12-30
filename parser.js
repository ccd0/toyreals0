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

function is_constant(token) {
  return /^\w/i.test(token);
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
  if (is_constant(token)) {
    result = token;
    i++;
  } else if ((op = prefix(token))) {
    [result, i] = parse_op(op, tokens, i);
  } else {
    throw 'parse error';
  }
  while (i < tokens.length) {
    token = tokens[i];
    if (is_constant(token)) {
      result = [result, token];
      i++;
    } else if ((op = infix(token))) {
      if (op[2] >= level) {
        let lhs = result;
        [result, i] = parse_op(op, tokens, i);
        result.splice(1, 0, lhs);
      } else {
        return [result, i];
      }
    } else if ((op = prefix(token))) {
      let arg;
      [arg, i] = parse_op(op, tokens, i);
      result = [result, arg];
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

return {tokenize, parse};

})();
