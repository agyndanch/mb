#!/usr/bin/env python3
"""
Substitution Test for Custom Shell
Uses the existing regex_driver to validate substitution command output against templates.
Supports debug mode using native bash implementation.
"""

import argparse
import io
import os
import subprocess
import sys
import tempfile
from pathlib import Path

from regex_driver import compare_output_with_template


def run_substitution_commands_with_shell(shell_path, commands, timeout=10):
    """
    Run a series of substitution commands with the specified shell.
    
    Args:
        shell_path: Path to the shell executable
        commands: List of command strings to execute
        timeout: Maximum time to wait for each command
    
    Returns:
        String containing all command outputs
    """
    # Filter out empty lines and comments
    filtered_commands = [cmd for cmd in commands if cmd.strip() and not cmd.strip().startswith('#')]
    
    try:
        # Run all commands in a single shell session to maintain state
        process = subprocess.Popen(
            [shell_path],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True
        )
        
        # Send all commands as a script
        script = '\n'.join(filtered_commands) + '\n'
        stdout, _ = process.communicate(input=script, timeout=timeout)
        
        return stdout.strip()
        
    except subprocess.TimeoutExpired:
        return f"TIMEOUT: Shell session timed out"
    except Exception as e:
        return f"ERROR: Shell session failed: {str(e)}"


def get_basic_expansion_test_commands():
    """
    Return basic expansion commands by reading from expansion_test_basic.sh file.
    These tests cover the essential functionality without complex nesting.
    """
    script_dir = Path(__file__).parent
    basic_script = script_dir / 'expansion_test_basic.sh'
    
    try:
        with open(basic_script, 'r') as f:
            lines = f.readlines()
        
        # Filter out shebang, comments, and empty lines to get just the commands
        commands = []
        for line in lines:
            line = line.strip()
            if line and not line.startswith('#') and not line.startswith('#!/'):
                commands.append(line)
        
        return commands
    except Exception as e:
        raise Exception(f"Error reading basic expansion test script: {str(e)}")


def get_advanced_expansion_test_commands():
    """
    Return advanced expansion commands with anti-hardcoding measures.
    Reads from expansion_test_advanced.sh which now generates its own dynamic values.
    """
    script_dir = Path(__file__).parent
    advanced_script = script_dir / 'expansion_test_advanced.sh'
    
    try:
        with open(advanced_script, 'r') as f:
            lines = f.readlines()
        
        # Filter out shebang, comments, and empty lines to get just the commands
        commands = []
        for line in lines:
            line = line.strip()
            if line and not line.startswith('#') and not line.startswith('#!/'):
                commands.append(line)
        
        return commands
    except Exception as e:
        raise Exception(f"Error reading advanced expansion test script: {str(e)}")


def run_expansion_test(shell_path, template_path, verbose=False, test_mode='both'):
    """
    Run the expansion test.
    
    Args:
        shell_path: Path to the shell to test
        template_path: Path to the regex template file (ignored for 'both' mode)
        verbose: If True, show detailed output on mismatch
        test_mode: 'basic', 'advanced', or 'both'
    
    Returns:
        Tuple of (success: bool, message: str)
    """
    if test_mode == 'basic':
        commands = get_basic_expansion_test_commands()
        test_description = "basic expansion"
        return _run_single_test(shell_path, template_path, commands, test_description, verbose)
    elif test_mode == 'advanced':
        commands = get_advanced_expansion_test_commands()
        test_description = "advanced expansion"
        return _run_single_test(shell_path, template_path, commands, test_description, verbose)
    elif test_mode == 'both':
        return _run_both_tests(shell_path, verbose)
    else:
        return False, f"Invalid test mode: {test_mode}. Use 'basic', 'advanced', or 'both'"


def _run_single_test(shell_path, template_path, commands, test_description, verbose):
    """Run a single test with the given commands and template."""
    
    # Check if shell exists
    if not os.path.exists(shell_path):
        return False, f"Shell not found: {shell_path}"
    
    if not os.access(shell_path, os.X_OK):
        return False, f"Shell not executable: {shell_path}"
    
    # Check if template exists
    if not os.path.exists(template_path):
        return False, f"Template file not found: {template_path}"
    
    print(f"Testing shell: {shell_path}")
    print(f"Using template: {template_path}")
    print(f"Test mode: {test_description}")
    print(f"Running {len([cmd for cmd in commands if cmd.strip() and not cmd.strip().startswith('#')])} expansion commands...")
    
    # Run commands with the custom shell
    try:
        actual_output = run_expansion_commands_with_shell(shell_path, commands)
        
        if verbose:
            print("\nActual output:")
            print("=" * 50)
            print(actual_output)
            print("=" * 50)
        
        # Create a temporary file with the actual output
        with tempfile.NamedTemporaryFile(mode='w', suffix='.txt', delete=False, encoding='utf-8') as tmp_file:
            tmp_file.write(actual_output)
            tmp_file_path = tmp_file.name
        
        try:
            # Use the regex driver to compare output with template
            with open(tmp_file_path, 'r', encoding='utf-8') as actual_file:
                success = compare_output_with_template(template_path, actual_file, verbose=verbose)
            
            if success:
                message = f"✓ SUCCESS: {test_description.capitalize()} test passed!"
            else:
                message = f"✗ FAILURE: {test_description.capitalize()} test failed."
            
            return success, message
            
        finally:
            # Clean up temporary file
            try:
                os.unlink(tmp_file_path)
            except OSError:
                pass
                
    except Exception as e:
        return False, f"Error running {test_description} test: {str(e)}"


def _run_both_tests(shell_path, verbose):
    """Run both basic and advanced tests separately."""
    
    # Check if shell exists
    if not os.path.exists(shell_path):
        return False, f"Shell not found: {shell_path}"
    
    if not os.access(shell_path, os.X_OK):
        return False, f"Shell not executable: {shell_path}"
    
    script_dir = Path(__file__).parent
    basic_template = script_dir / 'expansion_test_basic.reg'
    advanced_template = script_dir / 'expansion_test_advanced.reg'
    
    print(f"Testing shell: {shell_path}")
    print(f"Test mode: combined basic and advanced expansion")
    print(f"Running both basic and advanced tests separately...")
    
    # Run basic test
    print("\n" + "="*60)
    print("RUNNING BASIC TESTS")
    print("="*60)
    basic_commands = get_basic_expansion_test_commands()
    basic_success, basic_message = _run_single_test(
        shell_path, str(basic_template), basic_commands, "basic expansion", verbose
    )
    
    # Run advanced test
    print("\n" + "="*60)
    print("RUNNING ADVANCED TESTS")
    print("="*60)
    advanced_commands = get_advanced_expansion_test_commands()
    advanced_success, advanced_message = _run_single_test(
        shell_path, str(advanced_template), advanced_commands, "advanced expansion", verbose
    )
    
    # Combine results
    if basic_success and advanced_success:
        return True, f"✓ SUCCESS: Both basic and advanced tests passed!\n  Basic: {basic_message}\n  Advanced: {advanced_message}"
    elif basic_success:
        return False, f"✗ PARTIAL SUCCESS: Basic test passed, but advanced test failed.\n  Basic: {basic_message}\n  Advanced: {advanced_message}"
    elif advanced_success:
        return False, f"✗ PARTIAL SUCCESS: Advanced test passed, but basic test failed.\n  Basic: {basic_message}\n  Advanced: {advanced_message}"
    else:
        return False, f"✗ FAILURE: Both tests failed.\n  Basic: {basic_message}\n  Advanced: {advanced_message}"


def main():
    """Main function to run the expansion test."""
    parser = argparse.ArgumentParser(
        description="Test command expansion in custom shell with anti-hardcoding measures",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
This test includes comprehensive expansion testing with anti-hardcoding features:

Expansion Types Tested:
- Environment variables ($USER, $HOME, $PATH)
- Shell variables (custom set variables)
- Special builtin variables ($?, $$, $#, $*, $@, $0)
- Parameter expansion (${var}, ${var:-default}, ${#var}, etc.)
- Command substitution (backticks and $(...))
- Arithmetic expansion ($((expr)) and $[expr])
- Quote handling (single, double, mixed)
- Escape sequences
- Globbing and wildcards
- Tilde expansion (~, ~user, ~+, ~-)

Anti-Hardcoding Features:
- Dynamic random values that change each run
- Runtime-generated variable names and values
- Process-specific data (PID, timestamps)
- Complex nested expansions with computed results
- Real-time date/time expansions
- Multi-level arithmetic with random operands

Examples:
  python3 expansion_test.py --shell ./minibash                    # Run both basic and advanced tests
  python3 expansion_test.py --shell ./minibash -b                 # Run only basic tests  
  python3 expansion_test.py --shell ./minibash -a                 # Run only advanced tests
  python3 expansion_test.py --shell /bin/bash --verbose       # Run both tests with verbose output
        """
    )
    
    parser.add_argument(
        '--shell',
        default='./minibash',
        help='Path to the shell executable to test (default: ./minibash)'
    )
    
    parser.add_argument(
        '--template',
        default=None,
        help='Path to the regex template file (default: auto-select based on mode)'
    )
    
    # Create mutually exclusive group for test mode
    mode_group = parser.add_mutually_exclusive_group()
    mode_group.add_argument(
        '-b', '--basic',
        action='store_true',
        help='Run only basic expansion tests'
    )
    mode_group.add_argument(
        '-a', '--advanced',
        action='store_true',
        help='Run only advanced expansion tests with anti-hardcoding measures'
    )
    
    parser.add_argument(
        '--verbose', '-v',
        action='store_true',
        help='Show detailed output and diffs on mismatch'
    )
    
    args = parser.parse_args()
    
    # Convert to absolute paths
    script_dir = Path(__file__).parent
    shell_path = os.path.abspath(args.shell)
    
    # Determine test mode based on flags
    if args.basic:
        test_mode = 'basic'
    elif args.advanced:
        test_mode = 'advanced'
    else:
        test_mode = 'both'  # Default when no flags are specified
    
    # Auto-select template based on mode if not specified
    if test_mode == 'both':
        # For 'both' mode, template is handled internally
        success, message = run_echo_test(
            shell_path=shell_path,
            template_path=None,  # Not used for 'both' mode
            verbose=args.verbose,
            test_mode=test_mode
        )
    else:
        # For single mode tests, determine the template
        if args.template is None:
            if test_mode == 'basic':
                template_filename = 'expansion_test_basic.reg'
            elif test_mode == 'advanced':
                template_filename = 'expansion_test_advanced.reg'
        else:
            template_filename = args.template
        
        template_path = script_dir / template_filename
        
        success, message = run_expansion_test(
            shell_path=shell_path,
            template_path=str(template_path),
            verbose=args.verbose,
            test_mode=test_mode
        )
    
    print(f"\n{message}")
    
    sys.exit(0 if success else 1)


if __name__ == '__main__':
    main()
