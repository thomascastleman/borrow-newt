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

// First statement of the entire program
const first_statement = program.join(program_start_field);

const LINE_HEIGHT = 20;
const INDENT_AMOUNT = 20;
let x_offset = 20;
let y_offset = 20;

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

// Visualize a line of the program.
function visualizeLine(line, x_offset, y_offset) {
  d3.select(svg)
    .append("text")
    .style("fill", "black")
    .style("font-family", "monospace")
    .style("font-size", "16")
    .attr("x", x_offset)
    .attr("y", y_offset)
    .text(line);
}

// Convert a sequence of statements into Rust syntax
function convertToProgramText(starting_statement) {
  curr_statement = starting_statement;

  while (true) {
    // TODO: Convert this statement to string, add to text

    //statement is a declaration
    if (hasField(curr_statement, declared_variable_field)) {
      const variable = curr_statement.join(declared_variable_field);

      if (hasField(variable, mutable_field)) {
        text = "let mut " + variable + ";";
      } else {
        text = "let " + variable + ";";
      }

      visualizeLine(text, x_offset, y_offset);
    }

    //statement is an initialization
    else if (hasField(curr_statement, initialized_variable_field)) {
      const variable = curr_statement.join(initialized_variable_field);
      const value = curr_statement.join(initial_value_field);
      text = "" + variable + " = ";
      text += valueToString(value) + ";";
      visualizeLine(text, x_offset, y_offset);
    }

    //statement is an update
    else if (hasField(curr_statement, updated_variable_field)) {
      const variable = curr_statement.join(updated_variable_field);
      const value = curr_statement.join(new_value_field);
      text = variable + " = " + valueToString(value) + ";";
      visualizeLine(text, x_offset, y_offset);
    } else if (hasField(curr_statement, moved_value_field)) {
      const src = curr_statement.join(source_field);
      const dst = curr_statement.join(destination_field);

      if (hasField(curr_statement, destination_field)) {
        text = dst + " = " + src + ";";
      } else {
        text = "move_to_func(" + src + ");";
      }

      visualizeLine(text, x_offset, y_offset);
    } else if (!hasField(curr_statement, inner_scope_field)) {
      visualizeLine("{}", x_offset, y_offset);
    }
    y_offset += LINE_HEIGHT;

    // If there is an inner scope, convert that whole thing to text, add to text
    if (hasField(curr_statement, inner_scope_field)) {
      visualizeLine("{", x_offset, y_offset);
      y_offset += LINE_HEIGHT;
      x_offset += INDENT_AMOUNT;
      convertToProgramText(curr_statement.join(inner_scope_field));
      x_offset -= INDENT_AMOUNT;
      visualizeLine("}", x_offset, y_offset);
      y_offset += LINE_HEIGHT;
    }

    // Move to the next statement
    if (hasField(curr_statement, next_field)) {
      curr_statement = curr_statement.join(next_field);
    } else {
      break;
    }
  }
}

convertToProgramText(first_statement);
