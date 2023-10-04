#let enumerate(arr) = range(arr.len()).zip(arr)

#let tail(arr) = {
  let len = arr.len()
  enumerate(arr).filter(x => x.at(0) != 0).map(x => x.at(1))
}


#let width(body, styles) = {
  if type(body) == content {
    measure(body, styles).width
  }
  else if type(body) == array {
    body.map(x => width(x, styles)).sum()
  }
  else {
    measure([#body], styles).width
  }
}
#let height(body, styles) = {
  if type(body) == content {
    measure(body, styles).height
  }
  else if type(body) == array {
    body.map(x => height(x, styles)).sum()
  }
  else {
    measure([#body], styles).height
  }
}

#let ast_to_content_list(styles, maxlen, ast, neg, depth) = {
  // assert(type(ast) == array)
  if type(ast) == array {
    let contents = ast.map(b=>[#b])
    grid(
      columns: 2,
      gutter: maxlen - width(ast.at(0), styles) + 3em,
      ..contents
    )
  }
  else if type(ast) == dictionary {
    if ast.type == "box" {
      let nBoxes(arr) = {arr.filter(x => type(x) == dictionary).filter(x => x.type == "box").len()}
      let res = ast.children.map(x => {
        if type(x) == dictionary {
          ast_to_content_list(styles, maxlen - ast.indent, x, 0.6em * nBoxes(x.children) + neg*depth, depth+1)
        }
        else {
          ast_to_content_list(styles, maxlen - ast.indent, x, 0pt, depth+1)
        }
        }).flatten()
      let t = table(columns: 1, inset: 0.3em, ..res)
      let size = measure(t, styles)

      enumerate(res).map(x => {
        let (i,y) = x
        if i == 0 {
          let boxed(..more) = box(
                y,
                width: size.width + ast.indent,
                height: size.height + 0.6em - neg,
                inset: (y: 0pt, x: ast.indent),
                outset: (y: 3pt),
                ..more
              )
          place(
            if ast.stroke != auto {
              boxed(stroke: ast.stroke)
            }
            else {
              boxed()
            }
          )
        }
        else {
          box(
            y,
            inset: (x: ast.indent)
          )
        }
      })
    }

  }
}

#let maxlen(..bits, styles) = {
  let vals = bits.pos().map(b => {
    // assert(type(b) == array or type(b) == dictionary, message: "Array bits in fitch, got " + type(b))
    if type(b) == dictionary {
      if b.type == "box" {
        b.indent + maxlen(..b.children, styles)
      }
    }
    else if type(b) == array {
      width(b.at(0), styles)
    }
    else {
      assert(false, message: "Checking maxwidth of unknown type " + type(b))
    }
    }).flatten()
  calc.max(..vals)
}

#let helper_fitch(..bits, styles) = {
  let maxlen = maxlen(..bits, styles)
  let content = bits.pos().map(b => ast_to_content_list(styles, maxlen, b, 0pt, 1)).flatten()
  let table_bits = ()
  let lineno = 1

  while lineno <= content.len() {
      table_bits.push([#lineno])
      table_bits.push(content.at(lineno - 1))
      lineno = lineno + 1
  }
  table(
      columns: (18pt, 100%),
      // line spacing
      inset: 0.3em,
      stroke: none,
      ..table_bits
  )
}

#let fitch(..bits) = {
  style(styles => {
    helper_fitch(
      ..bits,
      styles
    )
  })
}

#let line(..bits) = {
  // let arr = bits.pos()
  // assert(arr.len() == 2)
  ($#bits.pos().first()$,)
  tail(bits.pos()).map(x => $#x$)
}

#let proof = fitch

#let con = [hello world]
#let b = table(con, stroke: 1pt + black, inset: 0.3em)

#con \
#style(styles => measure(con, styles))

#b \
#style(styles => measure(b, styles))

// stroke: auto - default behaviour of stroke for box
#let box(..bits, indent: 10pt, stroke: 0.7pt + black) = {
  (
    type: "box",
    indent: indent,
    stroke: stroke,
    children: bits.pos()
  )
}

#proof(
  box(
    line($forall x. forall y. P(x, y)$, [prem.]),
    box(
      stroke: red,
      line($x_0$, [fresh]),
      box(
        stroke: red,
        line($x_0$, [fresh]),
        line($forall x. forall y. P(x, y)$, [prem. what is this bro!]),
        line($x_0$, [fresh]),
        line($forall x. forall y. P(x, y)$, [prem. what is this bro!]),
        line($forall x. forall y. P(x, y)$, [prem.]),
        line($forall x. forall y. P(x, y)$, [prem.]),
      ),
        line($forall x. forall y. P(x, y)$, [prem.]),
        line($forall x. forall y. P(x, y)$, [prem.]),
      ),
      line($forall x. forall y. P(x, y)$, [prem.]),
    ),
    line($forall x. forall y. P(x, y)$, [prem.]),
  ),
  line($forall x. forall y. P(x, y)$, [prem.]),
)

// #proof(
//   line($p or q$, [LEM]),
//   box(
//     ($p and q$, [prem.]),
//     ($p -> q$, [prem.]),
//     ($forall x. (q and p <-> "hello world")$, [prem.]),
//     ($forall x. (q and p <-> "hello world")$, [prem.]),
//     ($forall x. (q and p <-> exists y. (P(y) and Q(x)))$, $forall_i 1, 2 "with" phi.alt = 2psi$),
//     ($1 + 2$,2),
//     ($forall x. (q and p <-> exists y. (P(y) and Q(x)))$, $forall_i 1, 2 "with" phi.alt = 2psi$),
//     ($forall x. (q and p <-> exists y. (P(y) and Q(x)))$, $forall_i 1, 2 "with" phi.alt = 2psi$),
//     box(
//       ($p or q$, [LEM]),
//       box(($p or q$, [LEM])),
//       box(($p$, [LEM])),
//       box(($p$, [LEM])),
//       box(($p$, [LEM])),
//       box(($p$, [LEM])),
//       box(($p$, [LEM])),
//       box(($p$, [LEM])),
//       box(($p$, [LEM])),
//       box(($p$, [LEM])),
//       ($p or q$, [LEM]),
//       ($forall x. (q and p <-> exists y. (P(y) and Q(x)))$, $forall_i 1, 2 "with" phi.alt = 2psi$),
//       ($p or q$, [LEM]),
//       ($p or q$, [LEM]),
//       ($p or q$, [LEM]),
//       ($p or q$, [LEM]),
//       )
//   ),
//   line($p or q$, [LEM]),
// )

