{.title}
# <h1 class="title">Slipshow Template</h1>

A comprehensive guide to all slipshow features

{pause up}

# How to Use This Template

This template teaches you every slipshow technique through examples.

{pause}

**Navigation controls:**

- **Space** or **→** : Next pause point
- **←** : Previous pause point
- **Escape** : Open table of contents

{pause}

**To build your slides:**

```bash
make
# or directly:
slipshow compile --theme oxcaml.css index.md
```

{pause}

When you're ready, delete all this content and write your own slides!

{pause up}

# 1. Basic Pauses

The `{pause}` command creates reveal points. Content after `{pause}` is hidden until you advance.

{pause}

**Example in markdown:**

```markdown
First point is visible immediately.

{pause}

This appears after pressing space/arrow.

{pause}

This appears on the next press.
```

{pause}

**Result:** Each paragraph above appeared one at a time.

{pause up}

# 2. Creating New Slides

Use `{pause up}` at the END of a section to create a new slide.

{pause}

**Example:**

```markdown
# Slide One

Content here...

{pause up}

# Slide Two

New slide starts here...
```

{pause}

The `# Heading` at the start of a slide becomes the blue title bar.

{pause}

**Other pause variants:**

| Command | Effect |
|---------|--------|
| `{pause}` | Simple reveal |
| `{pause up}` | New slide (scroll up) |
| `{pause center}` | Reveal and center content |
| `{pause down .classname}` | Reveal at bottom with class |

{pause up}

# 3. Adding IDs to Elements

The `{#your-id}` syntax assigns an HTML `id` attribute to the NEXT element.

{pause}

**Syntax:**

```markdown
{#my-paragraph}
This paragraph will have id="my-paragraph"
```

{pause}

**Resulting HTML:**

```html
<p id="my-paragraph">This paragraph will have id="my-paragraph"</p>
```

{pause}

**Why use IDs?**

IDs let you target specific elements with:
- JavaScript (for dynamic effects)
- CSS (for custom styling)

{pause}

**Example - targeting with CSS:**

```markdown
{#highlighted}
This text could be styled with #highlighted { color: red; }
```

{pause up}

# 4. Adding Classes to Elements

The `{.classname}` syntax adds CSS classes to the NEXT element.

{pause}

**Single class:**

```markdown
{.important}
This paragraph gets class="important"
```

{pause}

**Multiple classes:**

```markdown
{.important .centered .large}
This paragraph gets class="important centered large"
```

{pause}

**Combining ID and classes:**

```markdown
{#my-id .my-class}
This element has both an ID and a class.
```

{pause up}

# 5. Dynamic Scripting with {pause exec}

`{pause exec}` executes JavaScript code when you reach that pause point.

{pause}

**How it works:**

1. Write `{pause exec}`
2. Follow with a code block using language `slip-script`
3. The code runs when presentation reaches that point

{pause}

**Basic example:**

````markdown
{#target}
**Text to modify**

{pause exec}
```slip-script
let el = document.querySelector("#target")
slip.setStyle(el, "color", "blue")
```
````

{pause}

**Let's see it in action:**

{pause up}

# 6. Live Demo: Changing Styles

{#color-demo}
**Watch this text change color!**

{pause}

Press space to change it to blue...

{pause exec}
```slip-script
let el = document.querySelector("#color-demo")
slip.setStyle(el, "color", "blue")
```

{pause}

Now press space to change it to red...

{pause exec}
```slip-script
let el = document.querySelector("#color-demo")
slip.setStyle(el, "color", "red")
```

{pause}

And now green...

{pause exec}
```slip-script
let el = document.querySelector("#color-demo")
slip.setStyle(el, "color", "green")
```

{pause up}

# 7. The slip.setStyle() Function

**Syntax:**

```javascript
slip.setStyle(element, "cssProperty", "value")
```

{pause}

**Parameters:**

| Parameter | Description |
|-----------|-------------|
| `element` | DOM element (from querySelector) |
| `cssProperty` | CSS property in camelCase |
| `value` | New value as string |

{pause}

**Common CSS properties:**

```javascript
slip.setStyle(el, "color", "red")
slip.setStyle(el, "visibility", "visible")
slip.setStyle(el, "visibility", "hidden")
slip.setStyle(el, "display", "none")
slip.setStyle(el, "display", "block")
```

{pause up}

# 8. The slip.setClass() Function

**Syntax:**

```javascript
slip.setClass(element, "className", true)   // add class
slip.setClass(element, "className", false)  // remove class
```

{pause}

**Example - adding a class:**

````markdown
{#my-code}
```python
def example():
    pass
```

{pause exec}
```slip-script
let el = document.querySelector("#my-code")
slip.setClass(el, "does-not-compile", true)
```
````

{pause}

The `does-not-compile` class adds a red border (defined in oxcaml.css).

{pause up}

# 9. Live Demo: Adding Classes

{#code-to-mark}
```python
def broken():
    return 1 + "string"  # Type error!
```

{pause}

This code has a bug. Press space to mark it as an error...

{pause exec}
```slip-script
let el = document.querySelector("#code-to-mark")
slip.setClass(el, "does-not-compile", true)
```

{pause}

The red border indicates this code doesn't compile.

{pause up}

# 10. Styled Blocks

Slipshow supports special block types with colored headers.

{pause}

**Syntax:**

```markdown
{.definition title="Term Name"}
Your definition text here.
```

{pause}

**Available block types:**

{pause}

{.definition title="Definition"}
Use for defining terms or concepts. Blue header.

{pause}

{.theorem title="Theorem"}
Use for mathematical theorems. Pink background, italic text.

{pause}

{.remark title="Note"}
Use for important notes. Green styling.

{pause up}

# 11. More Block Types

{.corollary title="Corollary"}
Use for results that follow from theorems. Yellow styling.

{pause}

{.example title="Example"}
Use for practical examples. Green background.

{pause}

{.lemma title="Lemma"}
Use for helper results. Gray styling.

{pause}

**Block without title:**

```markdown
{.definition}
A definition without a custom title.
```

{pause up}

# 12. Question Layout (Comparisons)

Use `{.question}` to create side-by-side comparisons.

{pause}

**Horizontal layout:**

```markdown
{.question .horizontal}
> {#option-a}
> **Option A**
> Description of option A
>
> {#option-b}
> **Option B**
> Description of option B
```

{pause}

**Result:**

{.question .horizontal}
> {#demo-option-a}
> **Option A**
>
> First approach
>
> {#demo-option-b}
> **Option B**
>
> Second approach

{pause}

Now let's mark A as correct and B as wrong...

{pause exec}
```slip-script
let a = document.querySelector("#demo-option-a")
let b = document.querySelector("#demo-option-b")
slip.setClass(a, "correct", true)
slip.setClass(b, "wrong", true)
```

{pause}

The `correct` class adds a checkmark. The `wrong` class fades the element.

{pause up}

# 13. Vertical Question Layout

Use `{.question .vertical}` for top/bottom layout:

{pause}

{.question .vertical}
> {#top-option}
> **Top Option**
>
> This appears on top
>
> {#bottom-option}
> **Bottom Option**
>
> This appears below

{pause exec}
```slip-script
let top = document.querySelector("#top-option")
let bottom = document.querySelector("#bottom-option")
slip.setClass(top, "correct", true)
slip.setClass(bottom, "wrong", true)
```

{pause up}

# 14. Code Blocks

Standard fenced code blocks with syntax highlighting:

{pause}

```ocaml
let rec factorial n =
  if n <= 1 then 1
  else n * factorial (n - 1)
```

{pause}

```python
def factorial(n):
    if n <= 1:
        return 1
    return n * factorial(n - 1)
```

{pause}

```javascript
function factorial(n) {
  return n <= 1 ? 1 : n * factorial(n - 1);
}
```

{pause up}

# 15. Side-by-Side Code

Use HTML grid for side-by-side layouts:

{pause}

```html
<div style="display: grid; grid-template-columns: 1fr 1fr; gap: 1em;">

<!-- Left code block -->

<!-- Right code block -->

</div>
```

{pause}

**Result:**

<div style="display: grid; grid-template-columns: 1fr 1fr; gap: 1em;">

```python
# Python version
def greet(name):
    print(f"Hello, {name}")
```

```javascript
// JavaScript version
function greet(name) {
  console.log(`Hello, ${name}`);
}
```

</div>

{pause up}

# 16. Tables

Standard markdown tables:

{pause}

```markdown
| Column 1 | Column 2 | Column 3 |
|----------|----------|----------|
| Cell 1   | Cell 2   | Cell 3   |
| Cell 4   | Cell 5   | Cell 6   |
```

{pause}

**Result:**

| Column 1 | Column 2 | Column 3 |
|----------|----------|----------|
| Cell 1   | Cell 2   | Cell 3   |
| Cell 4   | Cell 5   | Cell 6   |

{pause up}

# 17. Lists

**Bullet lists:**

```markdown
- First item
- Second item
- Third item
```

{pause}

- First item
- Second item
- Third item

{pause}

**Nested lists:**

- Parent item
  - Child item
  - Another child
- Another parent

{pause up}

# 18. Inline HTML

You can embed any HTML directly in your slides:

{pause}

```html
<div style="background: linear-gradient(to right, #667eea, #764ba2);
            padding: 1em; border-radius: 10px; color: white;">
  <strong>Custom styled box</strong>
  <p>With gradient background</p>
</div>
```

{pause}

**Result:**

<div style="background: linear-gradient(to right, #667eea, #764ba2);
            padding: 1em; border-radius: 10px; color: white;">
  <strong>Custom styled box</strong>
  <p>With gradient background</p>
</div>

{pause up}

# 19. Images

**Markdown syntax:**

```markdown
![Alt text](./assets/image.svg)
```

{pause}

**HTML syntax (more control):**

```html
<img src="./assets/image.svg" width="200px" />
```

{pause}

**Positioned image:**

```html
<img style="position: absolute; top: 1em; right: 1em;"
     src="./assets/logo.svg" width="80px" />
```

{pause}

Place your images in an `assets/` folder.

{pause up}

# 20. Carousel (Image Sequences)

For stepping through images:

{pause}

```markdown
{carousel #my-carousel}
>> ![step 1](./assets/step1.svg)
> {change-page=my-carousel}
>> ![step 2](./assets/step2.svg)
> {change-page=my-carousel}
>> ![step 3](./assets/step3.svg)
```

{pause}

Each `{change-page=carousel-id}` advances to the next image.

{pause up}

# 21. Complete Example

Here's a full slide demonstrating multiple features:

{pause}

````markdown
# My Slide Title

Introduction paragraph.

{pause}

{.definition title="Key Concept"}
A concept is defined here.

{pause}

{#my-code}
```python
def example():
    return buggy_code()
```

{pause exec}
```slip-script
let el = document.querySelector("#my-code")
slip.setClass(el, "does-not-compile", true)
```

{pause}

{.remark title="Note"}
This code has a bug!

{pause up}
````

{pause up}

# Quick Reference

**Pause commands:**

| Command | Effect |
|---------|--------|
| `{pause}` | Reveal next content |
| `{pause up}` | New slide |
| `{pause center}` | Centered reveal |
| `{pause exec}` | Run script |

{pause}

**Element attributes:**

| Syntax | Effect |
|--------|--------|
| `{#my-id}` | Add id="my-id" |
| `{.my-class}` | Add class="my-class" |
| `{#id .class}` | Both |

{pause}

**Script functions:**

```javascript
slip.setStyle(el, "property", "value")
slip.setClass(el, "className", true/false)
```

{pause}

**Styled blocks:**

`.definition`, `.theorem`, `.remark`, `.corollary`, `.example`, `.lemma`

{pause up}

# Start Creating!

Delete everything in this file and write your own presentation.

{pause}

**Template files:**

- `index.md` - Your slides (this file)
- `oxcaml.css` - Theme with embedded fonts
- `Makefile` - Build command

{pause}

**Build:**

```bash
make
```

{pause}

**View:**

Open `index.html` in your browser.

