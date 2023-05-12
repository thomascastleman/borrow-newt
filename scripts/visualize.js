const d3 = require("d3");
d3.selectAll("svg > *").remove();

const SHOW_LINE_NUMBERS = true; // Whether to show line numbers
const EXPLICIT_LET_SCOPES = true; // Whether to show explicit curly braces/indentation for `let` scopes
const SHOW_LIFETIME_BOXES = true; // Whether to show the bounding boxes around lifetime regions
const SHOW_LABELS = true; // Whether to show additional metadata about the instance, for debugging
const LABELS_OFFSET = 50; // How much to the right of the program should the statement labels appear
const BASE_X_OFFSET = 35; // How much to offset in the X by default so that the program isn't partially cut off.
const BASE_Y_OFFSET = 20; // How much to offset in the Y by default so that the program isn't partially cut off.
const LINE_NO_OFFSET = 10; // How much to offset line numbers from left of window
const LINE_HEIGHT = 20; // The height of each line of text
const INDENT_AMOUNT = 20; // Size of indentation
const CENTERING_OFFSET = 5; // Offset for vertically centering the lifetime bounding boxes
const NESTING_OFFSET = 10; // Distance (pixels) between edges of nested lifetime boxes
const CHARACTER_WIDTH = 10; // Width of a character in pixels, roughly

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
const variable_type_field = instance.field("variable_type");
const value_lifetime_field = instance.field("value_lifetime");
const begin_field = instance.field("begin");
const end_field = instance.field("end");
const borrow_referent_type_field = instance.field("borrow_referent_type");
const borrow_mut_referent_type_field = instance.field(
  "borrow_mut_referent_type"
);

// First statement of the entire program
const first_statement = program.join(program_start_field);

class ProgramLine {
  constructor(text, indent_level, statement) {
    this.text = text;
    this.indent_level = indent_level;
    this.statement = statement;
  }
}

// Check if a sig has a given field defined.
function hasField(sig, field) {
  return sig.join(field).tuples().length != 0;
}

// Extract the number suffix from an object name (e.g. '4' from 'Variable4')
function numberFromObject(object) {
  const objectAsString = `${object}`;
  return objectAsString[objectAsString.length - 1];
}

// Convert a value object (owned, borrow, or borrow mut) to its visualization.
function valueToString(value) {
  if (hasField(value, borrow_field)) {
    return "&" + variableToString(value.join(borrow_field));
  } else if (hasField(value, borrow_mut_field)) {
    return "&mut " + variableToString(value.join(borrow_mut_field));
  } else {
    return `Box::new(${numberFromObject(value)})`;
  }
}

// Convert a type object to its visualization.
function typeToString(type) {
  if (hasField(type, borrow_referent_type_field)) {
    return "&" + typeToString(type.join(borrow_referent_type_field));
  } else if (hasField(type, borrow_mut_referent_type_field)) {
    return "&mut " + typeToString(type.join(borrow_mut_referent_type_field));
  } else {
    return "Box<i32>";
  }
}

// Convert a variable object to its visualization.
function variableToString(variable) {
  // Shorten variable names to v + number for brevity and less style warnings from rustc
  return `v${numberFromObject(variable)}`;
}

// Convert a sequence of statements into ProgramLines, which represent syntax.
function convertToLines(starting_statement, lines, indent_level) {
  let curr_statement = starting_statement;
  let text;

  while (true) {
    //statement is a declaration
    if (hasField(curr_statement, declared_variable_field)) {
      const variable = curr_statement.join(declared_variable_field);
      const typeString = typeToString(variable.join(variable_type_field));
      const mut = hasField(variable, mutable_field) ? "mut " : "";
      const variableString = variableToString(variable);

      text = "let " + mut + variableString + ": " + typeString + ";";

      lines.push(new ProgramLine(text, indent_level, curr_statement));
    }

    //statement is an initialization
    else if (hasField(curr_statement, initialized_variable_field)) {
      const variable = curr_statement.join(initialized_variable_field);
      const value = curr_statement.join(initial_value_field);
      text = variableToString(variable) + " = " + valueToString(value) + ";";
      lines.push(new ProgramLine(text, indent_level, curr_statement));
    }

    //statement is an update
    else if (hasField(curr_statement, updated_variable_field)) {
      const variable = curr_statement.join(updated_variable_field);
      const value = curr_statement.join(new_value_field);
      text = variableToString(variable) + " = " + valueToString(value) + ";";
      lines.push(new ProgramLine(text, indent_level, curr_statement));
    } else if (hasField(curr_statement, moved_value_field)) {
      const src = variableToString(curr_statement.join(source_field));

      if (hasField(curr_statement, destination_field)) {
        const dst = variableToString(curr_statement.join(destination_field));
        text = dst + " = " + src + ";";
      } else {
        text = "drop(" + src + ");";
      }

      lines.push(new ProgramLine(text, indent_level, curr_statement));
    } else if (!hasField(curr_statement, inner_scope_field)) {
      lines.push(new ProgramLine("{}", indent_level, curr_statement));
    }

    // If there is an inner scope, convert that whole thing to text, add to text
    if (hasField(curr_statement, inner_scope_field)) {
      const isLet = hasField(curr_statement, declared_variable_field);

      if (!isLet || EXPLICIT_LET_SCOPES) {
        // Show scope explicitly with surrounding braces and indentation
        lines.push(new ProgramLine("{", indent_level, curr_statement));
        convertToLines(
          curr_statement.join(inner_scope_field),
          lines,
          indent_level + 1
        );
        lines.push(new ProgramLine("}", indent_level, curr_statement));
      } else {
        // Use same indent level, no curly braces
        convertToLines(
          curr_statement.join(inner_scope_field),
          lines,
          indent_level
        );
      }
    }

    // Move to the next statement
    if (hasField(curr_statement, next_field)) {
      curr_statement = curr_statement.join(next_field);
    } else {
      break;
    }
  }
}

// Convert the given lines to a single string representing the entire program (with indentation).
function convertLinesToString(lines) {
  let programAsString = "";

  for (let i = 0; i < lines.length; i++) {
    programAsString +=
      "  ".repeat(lines[i].indent_level) + lines[i].text + "\n";
  }

  return programAsString;
}

// Find where in the given list of ProgramLines the given statement occurs
function indexOfStmtInLines(stmt, lines) {
  for (let i = 0; i < lines.length; i++) {
    // NOTE: We use numberFromObject here because the statement objects were not comparing equal properly
    if (numberFromObject(lines[i].statement) == numberFromObject(stmt)) {
      return i;
    }
  }

  return -1;
}

// Generate a random color, represented as a hex string.
function randomColor() {
  // Credit to https://stackoverflow.com/questions/1267283/how-can-i-pad-a-value-with-leading-zeros
  // for padding with leading 0s.
  return (
    "#" +
    ("000000" + Math.floor(Math.random() * Math.pow(2, 24)).toString(16)).slice(
      -6
    )
  );
}

// Extract all the value objects from the given program.
function valuesFromLines(lines) {
  let values = [];

  for (let i = 0; i < lines.length; i++) {
    const statement = lines[i].statement;

    if (statement) {
      let value;
      if (hasField(statement, initial_value_field)) {
        value = statement.join(initial_value_field);
      } else if (hasField(statement, new_value_field)) {
        value = statement.join(new_value_field);
      }

      if (value) {
        values.push(value);
      }
    }
  }

  return values;
}

// Display the text of the given program as lines of Rust code
function visualizeLines(lines, programWidth) {
  for (let i = 0; i < lines.length; i++) {
    const xOffset = BASE_X_OFFSET + lines[i].indent_level * INDENT_AMOUNT;
    const yOffset = BASE_Y_OFFSET + i * LINE_HEIGHT;

    let lineContent = lines[i].text;
    const statement = lines[i].statement;

    if (SHOW_LINE_NUMBERS) {
      d3.select(svg)
        .append("text")
        .style("fill", "gray")
        .style("font-family", "monospace")
        .style("font-size", "16")
        .attr("x", LINE_NO_OFFSET)
        .attr("y", yOffset)
        .text(i + 1);
    }

    // Show the visualized content of the statement
    d3.select(svg)
      .append("text")
      .style("fill", "black")
      .style("font-family", "monospace")
      .style("font-size", "16")
      .attr("x", xOffset)
      .attr("y", yOffset)
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
      }

      d3.select(svg)
        .append("text")
        .style("fill", "gray")
        .style("font-family", "monospace")
        .style("font-size", "16")
        .attr("x", BASE_X_OFFSET + programWidth + LABELS_OFFSET)
        .attr("y", yOffset)
        .text(label);
    }
  }
}

// Determine the "nestedness" of a value by counting how many other lifetimes its
// lifetime is fully contained within.
function valueNestedness(lifetimeBegin, lifetimeEnd, values, lines) {
  const beginIndex = indexOfStmtInLines(lifetimeBegin, lines);
  const endIndex = indexOfStmtInLines(lifetimeEnd, lines);
  let nestedness = 0;

  for (let i = 0; i < values.length; i++) {
    let otherValue = values[i];
    let otherLifetime = otherValue.join(value_lifetime_field);
    let otherLifetimeBegin = otherLifetime.join(begin_field);
    let otherLifetimeEnd = otherLifetime.join(end_field);

    let otherBeginIndex = indexOfStmtInLines(otherLifetimeBegin, lines);
    let otherEndIndex = indexOfStmtInLines(otherLifetimeEnd, lines);

    if (
      beginIndex >= otherBeginIndex &&
      beginIndex <= otherEndIndex &&
      endIndex >= otherBeginIndex &&
      endIndex <= otherEndIndex
    ) {
      nestedness++;
    }
  }

  return nestedness;
}

// Display the lifetimes in the given program with colored bounding boxes.
function visualizeLifetimes(lines, programWidth) {
  const values = valuesFromLines(lines);

  // Display what the lifetime is for each value in the instance,
  // below the program visualization.
  for (let i = 0; i < values.length; i++) {
    const labelXOffset = BASE_X_OFFSET;
    const labelYOffset = BASE_Y_OFFSET + (lines.length + i + 1) * LINE_HEIGHT;

    const lifetime = values[i].join(value_lifetime_field);
    const beginStmt = lifetime.join(begin_field);
    const endStmt = lifetime.join(end_field);

    const beginOffset = indexOfStmtInLines(beginStmt, lines) * LINE_HEIGHT;
    const endOffset = indexOfStmtInLines(endStmt, lines) * LINE_HEIGHT;

    const valueColor = randomColor();

    if (SHOW_LIFETIME_BOXES) {
      // Draw a box around the lifetime region
      d3.select(svg)
        .append("rect")
        .attr("x", BASE_X_OFFSET)
        .attr("y", CENTERING_OFFSET + beginOffset)
        .attr(
          "width",
          programWidth +
            LABELS_OFFSET -
            valueNestedness(beginStmt, endStmt, values, lines) * NESTING_OFFSET
        )
        .attr("height", endOffset - beginOffset + LINE_HEIGHT)
        .attr("fill-opacity", 0.2)
        .attr("fill", valueColor)
        .attr("stroke-width", 2)
        .attr("stroke-opacity", 1)
        .attr("stroke", valueColor);
    }

    if (SHOW_LABELS) {
      d3.select(svg)
        .append("text")
        .style("fill", valueColor)
        .style("font-family", "monospace")
        .style("font-size", "16")
        .attr("x", labelXOffset)
        .attr("y", labelYOffset)
        .text(`${values[i]} lives from ${beginStmt} to ${endStmt}`);
    }
  }
}

// Find the maximum width in pixels of any line in the given program.
function findMaxLineWidth(lines) {
  let maxWidth = null;

  for (let i = 0; i < lines.length; i++) {
    const width =
      lines[i].indent_level * INDENT_AMOUNT +
      lines[i].text.length * CHARACTER_WIDTH;

    if (maxWidth == null || width > maxWidth) {
      maxWidth = width;
    }
  }

  return maxWidth;
}

let lines = [];
convertToLines(first_statement, lines, 0);

// NOTE: Visualize the lifetime boxes *first*, then the program text on top of it,
// so that the text is more readable and doesn't get covered by the box colors.
const programWidth = findMaxLineWidth(lines);
visualizeLifetimes(lines, programWidth);
visualizeLines(lines, programWidth);

const programAsString = convertLinesToString(lines);

// Copy the program text to the clipboard, so it can be pasted and run if necessary
navigator.clipboard.writeText(programAsString);

// Log the program text to the console, in case automatic copying
// doesn't work, it can be copied from here.
console.log(programAsString);
