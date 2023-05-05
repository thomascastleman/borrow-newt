const d3 = require("d3");
d3.selectAll("svg > *").remove();

const program = instance.signature("Program").atoms()[0];
const program_start_field = instance.field("program_start");
const next_field = instance.field("next");
const inner_scope_field = instance.field("inner_scope");
const declared_variable_field = instance.field("declared_variable");
const initialized_variable_field = instance.field("initialized_variable");
const initial_value_field = instance.field("initial_value");
const updated_variable_field = instance.field("updated_variable");
const new_value_field = instance.field("new_value");
const moved_value_field = instance.field("moved_value");
const source_field = instance.field("source");
const destination_field = instance.field("destination");
const borrow_field = instance.field("borrow_referent");
const borrow_mut_field = instance.field("borrow_mut_referent");
const mutable_field = instance.field("mutable");
const value_lifetime_field = instance.field("value_lifetime");
const begin_field = instance.field("begin");
const end_field = instance.field("end");

// First statement of the entire program
const first_statement = program.join(program_start_field);

// Check if a sig has a given field defined.
function hasField(sig, field) {
  return sig.join(field).tuples().length != 0;
}

// Convert a value (owned, borrow, or borrow mut) to its visualization.
function valueToString(value) {
  if (hasField(value, borrow_field)) {
    return "&" + value.join(borrow_field);
  } else if (hasField(value, borrow_mut_field)) {
    return "&mut " + value.join(borrow_mut_field);
  } else {
    return value;
  }
}

class ProgramLine {
  constructor(text, indent_level, statement) {
    this.text = text;
    this.indent_level = indent_level;
    this.statement = statement;
  }
}

// Convert a sequence of statements into ProgramLines, which represent syntax.
function convertToLines(starting_statement, lines, indent_level) {
  let curr_statement = starting_statement;

  while (true) {
    // TODO: Add type information to declaration so it can be visualized
    //statement is a declaration
    if (hasField(curr_statement, declared_variable_field)) {
      const variable = curr_statement.join(declared_variable_field);

      if (hasField(variable, mutable_field)) {
        text = "let mut " + variable + ";";
      } else {
        text = "let " + variable + ";";
      }

      lines.push(new ProgramLine(text, indent_level, curr_statement));
    }

    //statement is an initialization
    else if (hasField(curr_statement, initialized_variable_field)) {
      const variable = curr_statement.join(initialized_variable_field);
      const value = curr_statement.join(initial_value_field);
      text = "" + variable + " = ";
      text += valueToString(value) + ";";
      lines.push(new ProgramLine(text, indent_level, curr_statement));
    }

    //statement is an update
    else if (hasField(curr_statement, updated_variable_field)) {
      const variable = curr_statement.join(updated_variable_field);
      const value = curr_statement.join(new_value_field);
      text = variable + " = " + valueToString(value) + ";";
      lines.push(new ProgramLine(text, indent_level, curr_statement));
    } else if (hasField(curr_statement, moved_value_field)) {
      const src = curr_statement.join(source_field);
      const dst = curr_statement.join(destination_field);

      if (hasField(curr_statement, destination_field)) {
        text = dst + " = " + src + ";";
      } else {
        text = "move_to_func(" + src + ");";
      }

      lines.push(new ProgramLine(text, indent_level, curr_statement));
    } else if (!hasField(curr_statement, inner_scope_field)) {
      lines.push(new ProgramLine("{}", indent_level, curr_statement));
    }

    // If there is an inner scope, convert that whole thing to text, add to text
    if (hasField(curr_statement, inner_scope_field)) {
      lines.push(new ProgramLine("{", indent_level, curr_statement));
      convertToLines(
        curr_statement.join(inner_scope_field),
        lines,
        indent_level + 1
      );
      lines.push(new ProgramLine("}", indent_level, curr_statement));
    }

    // Move to the next statement
    if (hasField(curr_statement, next_field)) {
      curr_statement = curr_statement.join(next_field);
    } else {
      break;
    }
  }
}

function convertLinesToString(lines) {
  let programAsString = "";

  for (let i = 0; i < lines.length; i++) {
    programAsString +=
      "  ".repeat(lines[i].indent_level) + lines[i].text + "\n";
  }

  return programAsString;
}

const SHOW_LABELS = true; // Whether to show additional metadata about the instance, for debugging
const LABELS_OFFSET = 350; // How much to offset the labels horizontally from the left
const BASE_OFFSET = 20; // How much to offset in the X/Y by default so that the program isn't partially cut off.
const LINE_HEIGHT = 20; // The height of each line of text
const INDENT_AMOUNT = 20; // Size of indentation

function visualizeLines(lines) {
  let values = [];

  for (let i = 0; i < lines.length; i++) {
    const x_offset = BASE_OFFSET + lines[i].indent_level * INDENT_AMOUNT;
    const y_offset = BASE_OFFSET + i * LINE_HEIGHT;

    let lineContent = lines[i].text;
    const statement = lines[i].statement;

    // Show the visualized content of the statement
    d3.select(svg)
      .append("text")
      .style("fill", "black")
      .style("font-family", "monospace")
      .style("font-size", "16")
      .attr("x", x_offset)
      .attr("y", y_offset)
      .text(lineContent);

    // Add annotations to the statement for debugging
    if (statement && SHOW_LABELS) {
      let label = statement;
      let value = null;

      if (hasField(statement, initial_value_field)) {
        value = statement.join(initial_value_field);
      } else if (hasField(statement, new_value_field)) {
        value = statement.join(new_value_field);
      }

      if (value) {
        label += " " + value;
        values.push(value);
      }

      d3.select(svg)
        .append("text")
        .style("fill", "gray")
        .style("font-family", "monospace")
        .style("font-size", "16")
        .attr("x", LABELS_OFFSET)
        .attr("y", y_offset)
        .text(label);
    }
  }

  if (SHOW_LABELS) {
    // Display what the lifetime is for each value in the instance,
    // below the program visualization.
    for (let i = 0; i < values.length; i++) {
      const x_offset = BASE_OFFSET;
      const y_offset = BASE_OFFSET + (lines.length + i + 1) * LINE_HEIGHT;

      const lifetime = values[i].join(value_lifetime_field);
      const beginStmt = lifetime.join(begin_field);
      const endStmt = lifetime.join(end_field);

      d3.select(svg)
        .append("text")
        .style("fill", "gray")
        .style("font-family", "monospace")
        .style("font-size", "16")
        .attr("x", x_offset)
        .attr("y", y_offset)
        .text(`${values[i]} lives from ${beginStmt} to ${endStmt}`);
    }
  }
}

let lines = [];
convertToLines(first_statement, lines, 0);
visualizeLines(lines);
const programAsString = convertLinesToString(lines);

// Copy the program text to the clipboard, so it can be pasted and run if necessary
navigator.clipboard.writeText(programAsString);

// Log the program text to the console, in case automatic copying
// doesn't work, it can be copied from here.
console.log(programAsString);
