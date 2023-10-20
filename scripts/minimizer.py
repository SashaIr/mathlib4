#!/usr/bin/env python3

import re
import logging
import shutil
import subprocess
import sys
import tempfile

def minimized_filename(original_file):
    name_parts = original_file.split('.')
    if len(name_parts) >= 3 and name_parts[-3] == 'min':
        try:
            version = int(name_parts[-2])
            return '.'.join(name_parts[:-3]) + f'.min.{version + 1}.lean'
        except ValueError:
            return '.'.join(name_parts[:-3]) + f'.min.1.lean'
    elif len(name_parts) >= 1 and name_parts[-1] == 'lean':
        return '.'.join(name_parts[:-1]) + f'.min.1.lean'
    else:
        return original_file + '.min.1.lean'

def make_definitive(original_file, current_file):
    new_file = minimized_filename(original_file)
    shutil.copyfile(current_file, new_file)
    return new_file

def delete_lineno(line):
    return re.sub('^[^:]+:[0-9]+:[0-9]+: ', '', line)

def delete_timeout_location(line):
    """Omit the precise point that a timeout occurred, because that's sensitive to generally irrelevant details."""
    return re.sub('\(deterministic\) timeout at \'[^\']+\'', 'deterministic timeout', line)

def erase_details(line):
    """Process a line of Lean stdout by erasing unnecessary details."""
    return delete_timeout_location(delete_lineno(line))

def ignore_sorry(lines):
    return [line for line in lines if line != 'warning: declaration uses \'sorry\'']

def substantially_similar(result_1, result_2):
    lines_1 = [erase_details(line) for line in result_1.stdout.split('\n')]
    lines_2 = [erase_details(line) for line in result_2.stdout.split('\n')]
    return ignore_sorry(lines_1) == ignore_sorry(lines_2)

def compile_file(filename):
    logging.debug(f"compile_file: {filename}")
    result = subprocess.run(
        ['lake', 'env', 'lean', filename],
        check=False, # We are expecting an error!
        capture_output=True,
        encoding='utf-8')
    #if result.stdout:
    #    logging.debug("compile_file: stdout =")
    #    logging.debug(result.stdout)
    if result.stderr:
        logging.info("compile_file: stderr =")
        logging.info(result.stderr)
    return result

def try_compile(expected_out, new_file):
    new_out = compile_file(new_file)
    return substantially_similar(expected_out, new_out)

def imports_in(source):
    for match in re.finditer(r'^import (.*)$', source, flags=re.MULTILINE):
        yield match.group(1)

def normalize_lean_code(source):
    """Do some minor transformations to fix easy errors, like duplicated or misplaced import statements."""

    # Organize imports.
    imports = sorted(set(imports_in(source)))
    import_statements = '\n'.join('import ' + import_name for import_name in imports)
    source = import_statements + '\n\n' + re.sub(r'^import (.*)$', '', source, flags=re.MULTILINE)

    # Delete empty lines
    source = re.sub(r'\n\n(\n)+', r'\n\n', source)

    return source

def apply_changes(changes, filename):
    with open(filename, 'r') as file:
        source = file.read()

    # Work backwards, otherwise we'll overwrite later changes.
    changed = False
    last_start = len(source)
    for start, end, replacement in sorted(changes, reverse=True):
        if start > end:
            logging.error(f"apply_changes: start should be less than end: ({start}, {end}, {replacement})")
        elif end > last_start:
            logging.warning(f"apply_changes: skipping change because it overlaps with previous ({last_start}): ({start}, {end}, {replacement})")
        elif source[start:end] == replacement:
            logging.warning(f"apply_changes: skipping change because it is identical to the original: ({start}, {end}, {replacement})")
        else:
            # logging.debug(f"apply_changes: (source[{start}:{end}] = {source[start:end]} -> {replacement})")
            source = source[:start] + replacement + source[end:]
            changed = True
            last_start = start

    if not changed:
        logging.warning(f"apply_changes: no changes applied")
        return False, filename

    source = normalize_lean_code(source)

    with tempfile.NamedTemporaryFile(mode='w', delete=False) as destination:
        logging.debug(f"apply_changes: {filename} -> {destination.name}")
        destination.write(source)
        return True, destination.name

def import_to_filename(import_name):
    return import_name.replace('.', '/') + '.lean'

def make_committing_pass(change_generator, bottom_up=False):
    """Turn a change generator into a minimization pass.

    A change generator will be called on a source file name and should return an iterable
    of all edits it wants to make, as a tuple (start, end, replacement)
    indicating that the substring source[start:end] should be replaced with the replacement.
    These changes should be independent, but they don't necessarily need to all make progress.

    The resulting minimization pass will try each change at most once and commit to the first that succeeds.
    By default, we try changes from the top of the file downwards.
    If `bottom_up` is true, then we try changes from the bottom of the file upwards.
    """
    def decomposable_pass(expected_out, filename):
        changes = sorted(list(change_generator(filename)), reverse=bottom_up)

        for i, change in enumerate(changes):
            logging.debug(f"committing_pass: trying change {i}")
            changed, new_file = apply_changes([change], filename)
            if not changed: continue

            if try_compile(expected_out, new_file):
                logging.info(f"committing_pass: change {i} succeeded")
                return True, new_file

        return False, filename

    return decomposable_pass

def make_bottom_up_pass(change_generator):
    """Turn a change generator into a minimization pass.

    A change generator will be called on a source file name and should return an iterable
    of all edits it wants to make, as a tuple (start, end, replacement)
    indicating that the substring source[start:end] should be replaced with the replacement.
    These changes should be independent, but they don't necessarily need to all make progress.

    The resulting minimization pass will go from the bottom to the top of the file to figure which subset of edits make progress,
    trying each change once.
    """
    def decomposable_pass(expected_out, filename):
        changes = sorted(list(change_generator(filename)))

        current_file = filename
        progress = False
        for i, change in reversed(list(enumerate(changes))):
            logging.debug(f"bottom_up_pass: trying change {i}")
            changed, new_file = apply_changes([change], current_file)
            if not changed: continue

            if try_compile(expected_out, new_file):
                logging.info(f"bottom_up_pass: change {i} succeeded")
                progress = True
                current_file = new_file

        return progress, current_file

    return decomposable_pass

def make_bisecting_pass(change_generator):
    """Turn a change generator into a minimization pass.

    A change generator will be called on a source file name and should return an iterable
    of all edits it wants to make, as a tuple (start, end, replacement)
    indicating that the substring source[start:end] should be replaced with the replacement.
    These changes should be independent, but they don't necessarily need to all make progress.

    The resulting minimization pass will use bisection to figure which subset of edits make progress.
    """

    def bisect_changes(expected_out, changes, filename):
        # Turn the change set from an iterable into a sorted list, so we can check for its length
        # and earlier changes apply to the earlier half of the file.
        # Moreover, sorting this list should help with determinism.
        changes = sorted(list(changes))

        if not changes:
            # Nothing to do, so no progress.
            logging.debug(f"bisect_changes: nothing to do here")
            return False, filename

        # Maybe the changes succeed instantly?
        logging.debug(f"bisect_changes: applying {len(changes)} changes")
        changed, new_file = apply_changes(changes, filename)
        if not changed: return False, filename
        if try_compile(expected_out, new_file):
            return True, new_file

        if len(changes) == 1:
            # The change didn't work, give up.
            return False, filename

        changes_top = changes[:len(changes) // 2]
        changes_bot = changes[len(changes) // 2:]

        # Otherwise, maybe there are some changes in the bottom half of the file that make progress.
        # We do the bottom half before the top half, since we can re-use the changes in the top half (while file indices in the bottom depend on those in the top)
        logging.debug(f"bisect_changes: trying to change the bottom half")
        progress_bot, file_bot = bisect_changes(expected_out, changes_bot, filename)
        if progress_bot:
            # Some progress in the bottom half, so try making progress in the top half too.
            logging.debug(f"bisect_changes: bottom half succeeded, let's try the top too")
            _, file_top_and_bot = bisect_changes(expected_out, changes_top, file_bot)
            # No matter whether we had progress in the top, we had progress in the bottom.
            return True, file_top_and_bot
        else:
            logging.debug(f"bisect_changes: trying to change only the top half")
            return bisect_changes(expected_out, changes_top, filename)

    def decomposable_pass(expected_out, filename):
        return bisect_changes(expected_out, change_generator(filename), filename)

    return decomposable_pass

def sequence_passes(*passes):
    """Apply minimization passes in sequence.

    Useful as an input to other pass combinators such as `loop_pass`.
    """
    def sequenced_pass(expected_out, filename):
        current_file = filename
        progress = False
        for minimize_pass in passes:
            pass_progress, new_file = minimize_pass(expected_out, current_file)
            if pass_progress:
                progress = True
                logging.info(f"sequence_passes: succeeded; continuing with {new_file}")
                current_file = new_file
        return progress, current_file

    return sequenced_pass

def loop_pass(minimize_pass):
    """Repeat a minimization pass until it no longer applies.

    Useful if you want to feed the output of a pass into itself.
    """
    def looping_pass(expected_out, filename):
        current_file = filename
        progress = False
        pass_progress = True
        while pass_progress:
            pass_progress, new_file = minimize_pass(expected_out, current_file)
            if pass_progress:
                progress = True
                logging.info(f"loop_pass: succeeded; repeating on {new_file}")
                current_file = new_file
        return progress, current_file

    return looping_pass

def strip_comments(filename):
    """Delete all comments from the source."""
    with open(filename, 'r') as file:
        source = file.read()

    for match in re.finditer(r'(^\s*)?\s--.*$',
                             # Require whitespace before, so we don't try to strip `/--` for example. Use .*$ to match until rest of the line, since '.' doesn't match newlines.
                             source,
                             flags=re.MULTILINE):
        yield match.start(), match.end(), ''

    # Block comments can be nested, so write an actual parser to count the nesting level.
    comment_level = 0
    comment_start = -1
    for start in range(len(source)):
        if source[start:start + len('/-')] == '/-':
            if comment_level == 0:
                comment_start = start
            comment_level += 1
        if source[start:start + len('-/')] == '-/':
            comment_end = start + len('-/')
            comment_level -= 1
            if comment_level < 0:
                # Syntax error? Give up trying to parse this comment.
                comment_level = 0
            elif comment_level == 0:
                # End of the outermost comment.
                yield comment_start, comment_end, ''

def delete_align(filename):
    """Delete all #align commands from the source."""
    with open(filename, 'r') as file:
        source = file.read()

    for match in re.finditer(r'#align .*$', source, flags=re.MULTILINE): # By default, '.' does not include newlines.
        yield match.start(), match.end(), ''
    for match in re.finditer(r'#align_import .*$', source, flags=re.MULTILINE): # By default, '.' does not include newlines.
        yield match.start(), match.end(), ''

def make_sorry(filename):
    """Replace ':= ...\n\n' with ':= sorry\n\n'"""
    with open(filename, 'r') as file:
        source = file.read()

    for match in re.finditer(r':=.*?\n\n', source, flags=re.DOTALL):
        if source[match.start():match.end()] == ':= sorry\n\n': continue # Skip useless changes.
        yield match.start(), match.end(), ':= sorry\n\n'

def make_proofs_sorry(filename):
    """Replace the proofs of theorems and lemmas (but not the value of `def`s) with `sorry`"""
    with open(filename, 'r') as file:
        source = file.read()

    for match in re.finditer(r'(theorem|lemma).*?(:=.*?\n\n)', source, flags=re.DOTALL):
        if match.group(2) == ':= sorry\n\n': continue # Skip useless changes.
        yield match.start(2), match.end(2), ':= sorry\n\n'

def delete_imports(filename):
    """Delete an import statement outright. Compare `replace_imports`."""
    with open(filename, 'r') as file:
        source = file.read()

    for match in re.finditer(r'^import (.*)$', source, flags=re.MULTILINE):
        yield match.start(), match.end(), ''

def replace_imports(filename):
    """Replace an import statement with just the imports of that file. Compare `delete_imports`."""
    with open(filename, 'r') as file:
        source = file.read()

    for match in re.finditer(r'^import (.*)$', source, flags=re.MULTILINE):
        import_name = match.group(1)
        import_filename = import_to_filename(import_name)
        try:
            with open(import_filename, 'r') as imported_file:
                replaced_imports = sorted(set(imports_in(imported_file.read())))
        except OSError:
            logging.warn(f"replace_imports: file not found: {import_filename}")
            continue
        import_source = '\n'.join(f'import {file}' for file in replaced_imports)

        logging.debug(f"replace_imports: import {import_name} -> {replaced_imports}")
        yield match.start(), match.end(), import_source

def include_imports(filename):
    """Replace an import statement with all the code in the file it imports. Compare `delete_imports`."""
    with open(filename, 'r') as file:
        source = file.read()

    for match in re.finditer(r'^import (.*)$', source, flags=re.MULTILINE):
        import_name = match.group(1)
        import_filename = import_to_filename(import_name)
        logging.debug(f"include_imports: import {import_name} -> <include {import_filename}>")
        try:
            with open(import_filename, 'r') as imported_file:
                import_source = imported_file.read()
        except OSError:
            logging.warn(f"include_imports: file not found: {import_filename}")
            continue
        yield match.start(), match.end(), '\n\nsection\n\n' + import_source + '\n\nend\n\n'

def delete_defs(filename):
    """Erase whole blocks of code delimited by two newlines.."""
    with open(filename, 'r') as file:
        source = file.read()

    for match in re.finditer(r'\n\n.*?\n\n', source, flags=re.DOTALL):
        yield match.start(), match.end(), '\n\n'

def delete_lines(filename):
    """Erase whole lines."""
    with open(filename, 'r') as file:
        source = file.read()

    for match in re.finditer(r'^.*$', source, flags=re.MULTILINE):
        yield match.start(), match.end(), ''

def combine_change_generators(*generators):
    """Return changes from both generators in an arbitrary order.

    Useful for when you want to choose between a fast but risky operation (e.g. deleting a declaration) and a slower but more likely operation (e.g. setting its value to sorry)."""
    def combined_generator(*args, **kwargs):
        for generator in generators:
            yield from generator(*args, **kwargs)
    return combined_generator

# Dictionary mapping pass-name to pass-code.
# Add more minimization passes here.
# The order matters: generally, you want the fast-to-finish passes to be on the top.
passes = {
    'strip_comments': make_bisecting_pass(strip_comments),
    'delete_align': make_bisecting_pass(delete_align),
    'make_proofs_sorry': make_bisecting_pass(make_proofs_sorry),
    'delete_or_sorry': make_bottom_up_pass(combine_change_generators(delete_defs, make_sorry)),
    'minimize_imports': loop_pass(sequence_passes(
        make_bisecting_pass(delete_imports),
        make_bisecting_pass(replace_imports))),
    'include_imports': make_committing_pass(include_imports),
}

def minimize_file(original_file):
    expected_out = compile_file(original_file)

    current_file = original_file
    progress = True
    while progress:
        progress = False

        for pass_name, minimize_pass in passes.items():
            logging.debug(f"minimize_file: running {pass_name} on {current_file}")
            try:
                pass_progress, new_file = minimize_pass(expected_out, current_file)
                if pass_progress:
                    logging.info(f"minimize_file: success: {pass_name} modified {current_file} -> {new_file}")
                    progress = True
                    # Commit to this intermediate result.
                    make_definitive(original_file, new_file)
                    current_file = new_file
            except Exception as e:
                logging.error(f"minimize_file: exception in {pass_name}: {e}")

    logging.debug(f"minimize_file: no more passes apply to {current_file}")
    return make_definitive(original_file, current_file)

if __name__ == "__main__":
    logging.basicConfig(level=logging.DEBUG)
    if len(sys.argv) < 2:
        print(f"usage: {sys.argv[0]} <testcase.lean>")
    else:
        original_file = sys.argv[1]
        logging.debug(f"minimize_file: output file will be {minimized_filename(original_file)}")
        min_file = minimize_file(original_file)
        print(min_file)
