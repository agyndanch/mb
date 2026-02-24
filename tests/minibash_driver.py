#!/usr/bin/env python3
"""
Generic minibash driver for running test scripts with corresponding .reg template files.
Each test script (e.g., echo_test.py) should have a corresponding .reg file (e.g., echo_test.reg).

Features:
- Configurable point system with default 70/30 basic/advanced split
- Individual test point configuration
- Category-based scoring and reporting
"""

import os
import sys
import subprocess
import glob
import time
from pathlib import Path
from dataclasses import dataclass
from typing import Dict, Tuple, Optional

# Grading constants
DEFAULT_TOTAL_POINTS = 100
DEFAULT_BASIC_RATIO = 0.7
VALGRIND_POINTS = 15


def create_progress_bar(current: int, total: int, width: int = 40) -> str:
    """
    Create a text-based progress bar.
    
    Args:
        current: Current progress value
        total: Total/maximum value
        width: Width of the progress bar in characters
    
    Returns:
        String representation of progress bar
    """
    if total == 0:
        return "[" + "─" * width + "]"
    
    percentage = current / total
    filled_width = int(width * percentage)
    bar = "█" * filled_width + "─" * (width - filled_width)
    return f"[{bar}]"


def format_progress_info(current: int, total: int, test_name: str = None, start_time: float = None) -> str:
    """
    Format progress information string.
    
    Args:
        current: Current test number (1-indexed)
        total: Total number of tests
        test_name: Optional name of current test
        start_time: Optional start time for elapsed time calculation
    
    Returns:
        Formatted progress string
    """
    percentage = (current / total * 100) if total > 0 else 0
    progress_bar = create_progress_bar(current, total, 30)
    
    info_parts = [
        f"Progress: {current}/{total} ({percentage:.1f}%)",
        progress_bar
    ]
    
    
    if test_name:
        info_parts.append(f"Running: {test_name}")
    
    return " | ".join(info_parts)


@dataclass
class TestConfig:
    """Configuration for individual tests and scoring."""
    name: str
    category: str  # 'basic', 'advanced', 'python', 'valgrind'
    points: int
    script_path: str
    expected_path: Optional[str] = None
    
    def __post_init__(self):
        """Convert paths to Path objects."""
        self.script_path = Path(self.script_path)
        if self.expected_path:
            self.expected_path = Path(self.expected_path)


class PointSystem:
    """Manages point distribution and scoring for tests."""
    
    def __init__(self, total_points: int = DEFAULT_TOTAL_POINTS, basic_ratio: float = DEFAULT_BASIC_RATIO, valgrind_points: int = VALGRIND_POINTS):
        """Initialize point system.
        
        Args:
            total_points: Base points for functional tests (basic/advanced/python)
            basic_ratio: Ratio of points for basic tests (0.0-1.0) 
            valgrind_points: Additional points for valgrind section (additive)
        """
        self.base_total_points = total_points  # Base points for functional tests
        self.valgrind_points = valgrind_points  # Additional points for valgrind
        
        # Distribute base points between basic/advanced (no reduction for valgrind)
        self.basic_ratio = basic_ratio
        self.advanced_ratio = 1.0 - basic_ratio
        
        self.basic_total = int(total_points * basic_ratio)
        self.advanced_total = total_points - self.basic_total
        
        # Track results
        self.results = {}
        self.test_configs = {}
        # Track valgrind results separately from test correctness
        self.valgrind_results = {}
        # Track whether valgrind is being used
        self.valgrind_enabled = False
        # Track which tests failed valgrind (but may have passed functionally)
        self.valgrind_failures = set()
        # Track proportional valgrind scoring ratio
        self.valgrind_score_ratio = 0.0
    
    def add_test_config(self, config: TestConfig):
        """Add a test configuration."""
        self.test_configs[config.name] = config
    
    def add_valgrind_test(self):
        """Add valgrind test configuration with allocated points."""
        self.valgrind_enabled = True
        valgrind_config = TestConfig(
            name="valgrind_memory_check",
            category='valgrind',
            points=self.valgrind_points,
            script_path="",  # Not applicable for valgrind meta-test
            expected_path=None
        )
        self.add_test_config(valgrind_config)
    
    @classmethod
    def create_for_category(cls, category: str, all_basic_tests: Dict, all_advanced_tests: Dict, 
                          all_python_tests: Dict = None, include_valgrind: bool = False):
        """Create a PointSystem for a specific category with correct proportional points.
        
        Args:
            category: 'basic', 'advanced', or 'python'
            all_basic_tests: Dict of all basic tests (for calculating proportions)
            all_advanced_tests: Dict of all advanced tests (for calculating proportions)
            all_python_tests: Dict of all python tests (for calculating proportions)
            include_valgrind: Whether to include valgrind points
            
        Returns:
            PointSystem instance with correct proportional points for the category
        """
        # Calculate the overall proportions based on all tests
        basic_count = len(all_basic_tests)
        advanced_count = len(all_advanced_tests)
        python_count = len(all_python_tests) if all_python_tests else 0
        
        # Create a reference point system to get the correct ratios
        ref_system = cls()
        ref_system.distribute_points(all_basic_tests, all_advanced_tests, all_python_tests)
        
        if category == 'basic':
            # Get the total points that basic tests should have
            basic_total_points = ref_system.basic_total
            point_system = cls(total_points=basic_total_points, basic_ratio=1.0)
            if include_valgrind:
                point_system.add_valgrind_test()
            point_system.distribute_points(all_basic_tests, {}, {})
            
        elif category == 'advanced':
            # Get the total points that advanced tests should have
            advanced_total_points = ref_system.advanced_total
            point_system = cls(total_points=advanced_total_points, basic_ratio=0.0)
            if include_valgrind:
                point_system.add_valgrind_test()
            point_system.distribute_points({}, all_advanced_tests, {})
            
        elif category == 'python':
            # Python tests get minimal points - use the same allocation as in distribute_points
            python_total_points = python_count  # 1 point per test
            point_system = cls(total_points=python_total_points, basic_ratio=0.0)
            if include_valgrind:
                point_system.add_valgrind_test()
            point_system.distribute_points({}, {}, all_python_tests)
            
        else:
            raise ValueError(f"Unknown category: {category}")
            
        return point_system
    
    def get_total_possible_points(self):
        """Get total possible points based on whether valgrind is enabled."""
        if self.valgrind_enabled:
            return self.base_total_points + self.valgrind_points
        else:
            return self.base_total_points
    
    def distribute_points(self, basic_tests: Dict, advanced_tests: Dict, python_tests: Dict = None):
        """Distribute points among tests based on categories.
        
        Args:
            basic_tests: Dict of basic test names -> (script_path, expected_path)
            advanced_tests: Dict of advanced test names -> (script_path, expected_path)
            python_tests: Dict of python test names -> (script_path, expected_path)
        """
        # Count tests in each category
        basic_count = len(basic_tests)
        advanced_count = len(advanced_tests)
        python_count = len(python_tests) if python_tests else 0
        
        # Distribute points evenly within categories
        basic_points_per_test = self.basic_total // basic_count if basic_count > 0 else 0
        advanced_points_per_test = self.advanced_total // advanced_count if advanced_count > 0 else 0
        
        # Handle remainder points
        basic_remainder = self.basic_total % basic_count if basic_count > 0 else 0
        advanced_remainder = self.advanced_total % advanced_count if advanced_count > 0 else 0
        
        # Create test configs for basic tests
        for i, (test_name, (script_path, expected_path)) in enumerate(basic_tests.items()):
            points = basic_points_per_test + (1 if i < basic_remainder else 0)
            config = TestConfig(
                name=test_name,
                category='basic',
                points=points,
                script_path=str(script_path),
                expected_path=str(expected_path) if expected_path else None
            )
            self.add_test_config(config)
        
        # Create test configs for advanced tests
        for i, (test_name, (script_path, expected_path)) in enumerate(advanced_tests.items()):
            points = advanced_points_per_test + (1 if i < advanced_remainder else 0)
            config = TestConfig(
                name=test_name,
                category='advanced', 
                points=points,
                script_path=str(script_path),
                expected_path=str(expected_path) if expected_path else None
            )
            self.add_test_config(config)
        
        # Handle Python tests (assign minimal points or distribute from basic pool)
        if python_tests:
            python_points_per_test = 1  # Minimal points for python tests
            for test_name, (script_path, reg_path) in python_tests.items():
                config = TestConfig(
                    name=test_name,
                    category='python',
                    points=python_points_per_test,
                    script_path=str(script_path),
                    expected_path=str(reg_path)
                )
                self.add_test_config(config)
    
    def record_result(self, test_name: str, passed: bool):
        """Record test result."""
        self.results[test_name] = passed
    
    def record_valgrind_result(self, test_name: str, no_memory_leaks: bool):
        """Record valgrind result (separate from test correctness)."""
        self.valgrind_results[test_name] = no_memory_leaks
        if not no_memory_leaks:
            self.valgrind_failures.add(test_name)
    
    def test_failed_valgrind(self, test_name: str) -> bool:
        """Check if a test failed valgrind (but may have passed functionally)."""
        return test_name in self.valgrind_failures
    
    def evaluate_valgrind_results(self):
        """Evaluate valgrind tests and record overall valgrind score."""
        # Calculate proportional score: A/n where A = tests passed, n = total tests
        if not self.valgrind_results:
            # No valgrind results recorded
            self.record_result("valgrind_memory_check", False)
            return
            
        total_tests = len(self.valgrind_results)
        passed_tests = sum(1 for result in self.valgrind_results.values() if result)
        
        # Calculate the proportion of tests that passed valgrind
        # This will be used to scale the valgrind points accordingly
        valgrind_score_ratio = passed_tests / total_tests if total_tests > 0 else 0
        
        #print(f"DEBUG: Valgrind results: {passed_tests}/{total_tests} passed ({valgrind_score_ratio:.2%})")
        
        # Store the proportional result - we'll handle fractional scoring in get_score()
        self.valgrind_score_ratio = valgrind_score_ratio
        # For compatibility, record as passed if all tests passed
        self.record_result("valgrind_memory_check", valgrind_score_ratio == 1.0)
    
    def get_score(self, category: str = None) -> Tuple[int, int]:
        """Get current score for category or overall.
        
        Args:
            category: 'basic', 'advanced', 'python', 'valgrind', or None for overall
            
        Returns:
            Tuple of (earned_points, total_possible_points)
        """
        earned = 0
        total = 0
        
        for test_name, config in self.test_configs.items():
            if category is None or config.category == category:
                # For valgrind tests, only include in scoring if valgrind was actually run
                if config.category == 'valgrind' and test_name not in self.results:
                    # Valgrind test exists but was never run - don't count it
                    continue
                
                total += config.points
                
                # Handle proportional valgrind scoring
                if config.category == 'valgrind' and hasattr(self, 'valgrind_score_ratio'):
                    # Use proportional scoring: earned = total_points * (passed_tests / total_tests)
                    earned += int(config.points * self.valgrind_score_ratio)
                elif self.results.get(test_name, False):
                    earned += config.points
        
        return earned, total
    
    def get_summary(self) -> str:
        """Generate scoring summary."""
        lines = []
        lines.append("\n" + "-" * 70 + "\nFinal Score\n" + "-" * 70)
        
        # Category breakdown
        for category in ['basic', 'advanced', 'python', 'valgrind']:
            earned, total = self.get_score(category)
            if total > 0:
                percentage = (earned / total) * 100
                lines.append(f"  {category.title()}: {earned}/{total} ({percentage:.1f}%)")
        
        # Overall score
        earned, total = self.get_score()
        percentage = (earned / total) * 100 if total > 0 else 0
        lines.append(f"  Overall: {earned}/{total} ({percentage:.1f}%)")
        
        return '\n'.join(lines)
from dataclasses import dataclass
from typing import Dict, Tuple, Optional


def create_table_header():
    """Create table header for test results."""
    header_line = "=" * 70
    header_row = "| {:<45} | {:<18} |".format("Test Results", "Points")
    return f"{header_line}\n{header_row}"


def create_table_row(test_name, points_text, success=True, valgrind_failed=False):
    """Create a table row for test results."""
    # Add visual indicator for pass/fail
    indicator = "✓" if success else "✗"
    # Add valgrind failure indicator
    if valgrind_failed and success:
        indicator = "⚠"  # Warning symbol for tests that pass but fail valgrind
        test_with_indicator = f"{indicator} {test_name} (valgrind failed)"
    else:
        test_with_indicator = f"{indicator} {test_name}"
    return "| {:<45} | {:<18} |".format(test_with_indicator[:45], points_text)


def create_table_section_divider(section_name, add_top_separator=True):
    """Create a section divider within the table."""
    divider_line = "+" + "-" * 47 + "+" + "-" * 20 + "+"
    section_row = "| {:<45} | {:<18} |".format(f"--- {section_name} ---", "")
    
    if add_top_separator:
        return f"{divider_line}\n{section_row}\n{divider_line}"
    else:
        return f"{section_row}\n{divider_line}"


def create_table_footer():
    """Create table footer."""
    return "=" * 70


def execute_and_display_test(test_name, test_runner_func, test_args, point_system, 
                           current_test, total_tests, start_time, verbose, all_output, valgrind=False, valgrind_failed=False):
    """
    Unified function to execute a test and display its result in either verbose or table format.
    
    Args:
        test_name: Name of the test
        test_runner_func: Function to run the test (run_test or run_sh_test)
        test_args: Arguments to pass to the test runner function
        point_system: PointSystem instance for scoring
        current_test: Current test number (1-indexed)
        total_tests: Total number of tests
        start_time: Start time for elapsed time calculation
        verbose: Whether to show verbose output
        all_output: List to append output lines to
        valgrind: Whether to run with valgrind (affects test name display)
    
    Returns:
        Tuple of (success: bool, test_output: str)
    """
    # Show progress indicator
    if not verbose:
        progress_info = format_progress_info(current_test, total_tests, test_name, start_time)
        print(f"\r{progress_info}", end="", flush=True)
    else:
        print(f"Running test {current_test}/{total_tests}: {test_name}")
    
    # Run the test
    success, output = test_runner_func(*test_args)
    
    # Record result in point system
    point_system.record_result(test_name, success)
    
    if not verbose:
        # Create table row
        if test_name in point_system.test_configs:
            points = point_system.test_configs[test_name].points
            earned = points if success else 0
            points_text = f"{earned}/{points} pts"
        else:
            points_text = "N/A"
        
        table_row = create_table_row(test_name, points_text, success, valgrind_failed)
        print(f"\r{' ' * 120}\r{table_row}")
        all_output.append(table_row)
        
        # Show progress indicator between tests if not the last test
        if current_test < total_tests:
            next_progress_info = format_progress_info(current_test, total_tests, None, start_time)
            print(f"\r{next_progress_info}", end="", flush=True)
    else:
        # In verbose mode, only show details for failed tests
        if success:
            status = "PASS"
            if test_name in point_system.test_configs:
                points = point_system.test_configs[test_name].points
                print(f"  {status}: {test_name} ({points}/{points} pts)")
            else:
                print(f"  {status}: {test_name}")
        else:
            status = "FAIL"
            if test_name in point_system.test_configs:
                points = point_system.test_configs[test_name].points
                print(f"  {status}: {test_name} (0/{points} pts)")
            else:
                print(f"  {status}: {test_name}")
            # Show full details for failed tests
            print(f"    Details: {output}")
            print("-" * 60)
    
    return success, output


def print_section_header(section_name, verbose, all_output, add_top_separator=True):
    """
    Print section header in either verbose or table format.
    
    Args:
        section_name: Name of the section
        verbose: Whether to show verbose output
        all_output: List to append output lines to
        add_top_separator: Whether to add top separator for table
    """
    if not verbose:
        # Clear any existing progress bar before printing section divider
        print(f"\r{' ' * 120}\r", end="")
        section_divider = create_table_section_divider(section_name, add_top_separator)
        print(section_divider)
        all_output.append(section_divider)
    else:
        print(f"\n=== {section_name} ===\n")


def print_score_summary(point_system, verbose, all_output):
    """
    Print final score summary in either verbose or table format.
    
    Args:
        point_system: PointSystem instance for scoring
        verbose: Whether to show verbose output
        all_output: List to append output lines to
    """
    if not verbose:
        # Clear any existing progress bar before printing final score
        print(f"\r{' ' * 120}\r", end="")
        # Add final score section to table
        final_score_divider = create_table_section_divider("Final Score")
        print(final_score_divider)
        all_output.append(final_score_divider)
        
        # Add score breakdown as table rows
        categories_with_scores = []
        for category in ['basic', 'advanced', 'python', 'valgrind']:
            earned, total = point_system.get_score(category)
            if total > 0:
                categories_with_scores.append(category)
                percentage = (earned / total) * 100
                score_text = f"{earned}/{total} ({percentage:.1f}%)"
                score_row = create_table_row(f"{category.title()} Tests", score_text, earned == total)
                print(score_row)
                all_output.append(score_row)
        
        # Add overall score only if multiple categories are present
        if len(categories_with_scores) > 1:
            earned, total = point_system.get_score()
            percentage = (earned / total) * 100 if total > 0 else 0
            score_text = f"{earned}/{total} ({percentage:.1f}%)"
            overall_score_row = create_table_row("Overall Score", score_text, earned == total)
            print(overall_score_row)
            all_output.append(overall_score_row)
        
        # Print table footer
        table_footer = create_table_footer()
        print(table_footer)
        all_output.append(table_footer)
    else:
        # In verbose mode, show simpler summary
        print("\n" + "=" * 60)
        print("FINAL SCORE SUMMARY")
        print("=" * 60)
        
        categories_with_scores = []
        for category in ['basic', 'advanced', 'python', 'valgrind']:
            earned, total = point_system.get_score(category)
            if total > 0:
                categories_with_scores.append(category)
                percentage = (earned / total) * 100
                status = "✓" if earned == total else "✗"
                print(f"{status} {category.title()} Tests: {earned}/{total} ({percentage:.1f}%)")
        
        # Show overall score only if multiple categories are present
        if len(categories_with_scores) > 1:
            earned, total = point_system.get_score()
            percentage = (earned / total) * 100 if total > 0 else 0
            status = "✓" if earned == total else "✗"
            print(f"\n{status} Overall Score: {earned}/{total} ({percentage:.1f}%)")
        print("=" * 60)


def cleanup_core_files(script_dir):
    """
    Clean up core.die files generated by crash tests.
    
    Args:
        script_dir: Directory to clean up
    """
    try:
        core_files = glob.glob(str(script_dir / "core.die.*"))
        if len(core_files) > 0:
            for core_file in core_files:
                os.remove(core_file)
            print(f"Cleaned up {len(core_files)} core.die files")
    except Exception as e:
        print(f"Warning: Could not clean up core files: {e}")




def discover_tests(script_dir):
    """
    Discover all available test scripts and their corresponding .reg files.
    
    Args:
        script_dir: Directory to search for test files
    
    Returns:
        Dict mapping test names to (script_path, reg_path) tuples
    """
    tests = {}
    test_scripts = glob.glob(str(script_dir / "*_test.py"))
    
    # Exclude standalone test scripts that don't follow the *_test.py + .reg pattern
    excluded_scripts = {'substitution_test.py'}
    
    for script_path in test_scripts:
        script_path = Path(script_path)
        test_name = script_path.stem  # e.g., "echo_test"
        
        # Skip excluded scripts
        if script_path.name in excluded_scripts:
            continue
            
        reg_path = script_dir / f"{test_name}.reg"
        
        if reg_path.exists():
            tests[test_name] = (script_path, reg_path)
        else:
            print(f"Warning: No .reg file found for {script_path}")
    
    return tests


def discover_sh_tests(script_dir):
    """
    Discover all .sh test scripts and their corresponding .out or .reg files.
    
    Args:
        script_dir: Directory to search for test files
    
    Returns:
        Dict mapping categories to test dictionaries:
        {
            'basic': {test_name: (script_path, expected_path), ...},
            'advanced': {test_name: (script_path, expected_path), ...}
        }
    """
    sh_tests = {"basic": {}, "advanced": {}}
    test_scripts = glob.glob(str(script_dir / "*.sh"))
    
    for script_path in test_scripts:
        script_path = Path(script_path)
        test_name = script_path.stem  # e.g., "001-comment" or "substitution_test_basic"
        
        # Look for .out file first, then .reg file
        out_path = script_dir / f"{test_name}.out"
        reg_path = script_dir / f"{test_name}.reg"
        
        expected_path = None
        if out_path.exists():
            expected_path = out_path
        elif reg_path.exists():
            expected_path = reg_path
        
        if expected_path:
            # Categorize based on test number or name
            if test_name.startswith("substitution_test_"):
                # Handle substitution tests
                if "basic" in test_name:
                    category = "basic"
                else:
                    category = "advanced"
            else:
                # Handle numbered tests (basic: 001-099, advanced: 100+)
                try:
                    test_num = int(test_name.split('-')[0])
                    category = "basic" if test_num < 100 else "advanced"
                except (ValueError, IndexError):
                    # If we can't parse the number, default to basic
                    category = "basic"
            
            sh_tests[category][test_name] = (script_path, expected_path)
        else:
            print(f"Warning: No .out or .reg file found for {script_path}")
    
    return sh_tests




def run_test(test_name, script_path, shell_path="./minibash", verbose=False, valgrind=False):
    """
    Run a specific test script with the given shell.
    
    Args:
        test_name: Name of the test (e.g., "echo_test")
        script_path: Path to the test script
        shell_path: Path to the shell executable to test
        verbose: Whether to show verbose output
        valgrind: Whether to run with valgrind memory leak checking
    
    Returns:
        Tuple of (success: bool, output: str)
    """
    try:
        # Prepend valgrind command if requested
        if valgrind:
            shell_cmd = ["valgrind", "--leak-check=full", shell_path]
        else:
            shell_cmd = [shell_path]
        
        cmd = ["python3", str(script_path), "--shell"] + shell_cmd
        if verbose:
            cmd.append("--verbose")
        
        os.environ['PATH'] = f'{script_path.parent}{os.pathsep}{os.environ["PATH"]}'
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
        )
        
        return result.returncode == 0, result.stdout + result.stderr
        
    except Exception as e:
        return False, f"Error running {test_name}: {str(e)}"


def run_valgrind_on_shell(script_path, shell_path="./minibash"):
    """
    Run valgrind on a shell script and return the raw valgrind output.
    
    Args:
        script_path: Path to the .sh script
        shell_path: Path to the shell executable to test
    
    Returns:
        Tuple of (success: bool, valgrind_output: str)
    """
    try:
        cmd = ["valgrind", "--leak-check=full", "--error-exitcode=1", shell_path, str(script_path)]
        
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=30
        )
        
        # Return success and the stderr output which contains valgrind info
        return result.returncode == 0, result.stderr
        
    except subprocess.TimeoutExpired:
        return False, "TIMEOUT: Valgrind check exceeded 30 seconds"
    except Exception as e:
        return False, f"Error running valgrind: {str(e)}"


def check_valgrind_for_leaks(output):
    """
    Check valgrind output for memory leaks.
    
    Args:
        output: Combined stdout and stderr from valgrind execution
    
    Returns:
        bool: True if no memory leaks detected, False if leaks found
    """
    lines = output.split('\n')
    found_valgrind = False
    
    for line in lines:
        line = line.strip()
        
        # Check if this is valgrind output
        if "Memcheck, a memory error detector" in line:
            found_valgrind = True
        
        # Check for clean exit - no leaks possible
        if "All heap blocks were freed -- no leaks are possible" in line:
            return True
        
        # Check for any actual leaks (non-zero bytes lost)
        if "definitely lost:" in line and not "0 bytes" in line:
            return False
        
        if "possibly lost:" in line and not "0 bytes" in line:
            return False
    
    # If we found valgrind output but no leaks were detected, assume clean
    if found_valgrind:
        return True
    
    # If no valgrind output detected, assume it didn't run with valgrind
    return False




def run_sh_test(test_name, script_path, expected_path, shell_path="./minibash", verbose=False, valgrind=False):
    """
    Run a .sh test script and compare output with expected .out or .reg file.
    
    Args:
        test_name: Name of the test (e.g., "001-comment")
        script_path: Path to the .sh script
        expected_path: Path to the expected .out or .reg file
        shell_path: Path to the shell executable to test
        verbose: Whether to show verbose output
        valgrind: Whether to run with valgrind memory leak checking
    
    Returns:
        Tuple of (success: bool, output: str)
    """
    try:
        # Run the shell script with the specified shell
        if valgrind:
            cmd = ["valgrind", "--leak-check=full", shell_path, str(script_path)]
        else:
            cmd = [shell_path, str(script_path)]
        
        os.environ['PATH'] = f'{script_path.parent}{os.pathsep}{os.environ["PATH"]}'
        
        # Check if this is a timing-sensitive while complex test
        timing_sensitive_tests = ["200-while-complex", "201-while-complex-2"]
        
        if test_name in timing_sensitive_tests:
            # For timing-sensitive tests, use Popen with a reasonable timeout
            process = subprocess.Popen(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True
            )
            
            try:
                # Use communicate() with timeout to prevent hanging
                # Allow extra time for the timing-sensitive tests to complete
                # 200-while-complex runs for 5 seconds, 201-while-complex-2 runs for 3 seconds
                timeout_seconds = 15  # Give extra buffer time
                stdout, stderr = process.communicate(timeout=timeout_seconds)
                
                actual_output = stdout
                result_returncode = process.returncode
                result_stderr = stderr
            except subprocess.TimeoutExpired:
                # If the process times out, kill it and return failure
                process.kill()
                stdout, stderr = process.communicate()
                return False, f"TIMEOUT: {test_name} exceeded {timeout_seconds} seconds (process may have hung)"
        else:
            # For other tests, use the original approach with timeout
            timeout = 30  # Allow up to 30 seconds for tests to complete
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=timeout
            )
            actual_output = result.stdout
            result_returncode = result.returncode
            result_stderr = result.stderr
        
        # Check if this is a .reg file (regex-based) or .out file (exact match)
        if expected_path.suffix == '.reg':
            # For .reg files, use regex validation from regex_driver
            try:
                # Import the regex validation function
                import sys
                sys.path.insert(0, str(script_path.parent))
                from regex_driver import compare_output_with_template
                
                # Create a temporary file with the actual output for regex validation
                import tempfile
                with tempfile.NamedTemporaryFile(mode='w', suffix='.txt', delete=False, encoding='utf-8') as tmp_file:
                    tmp_file.write(actual_output)
                    tmp_file_path = tmp_file.name
                
                try:
                    # Use the regex driver to compare output with template
                    with open(tmp_file_path, 'r', encoding='utf-8') as actual_file:
                        success = compare_output_with_template(str(expected_path), actual_file, verbose=verbose)
                    
                    output = f"{'PASS' if success else 'FAIL'}: {test_name}"
                    
                    if verbose or not success:
                        output += f"\nActual output:\n{repr(actual_output)}"
                        if result_stderr:
                            output += f"\nStderr:\n{result_stderr}"
                            
                finally:
                    # Clean up temporary file
                    try:
                        os.unlink(tmp_file_path)
                    except OSError:
                        pass
                        
            except Exception as e:
                success = False
                output = f"FAIL: {test_name} (regex validation error: {str(e)})"
                if verbose:
                    output += f"\nActual output:\n{repr(actual_output)}"
                    if result_stderr:
                        output += f"\nStderr:\n{result_stderr}"
        else:
            # For .out files, do exact comparison with expected output
            with open(expected_path, 'r') as f:
                expected_output = f.read()
            
            success = actual_output == expected_output
            
            if success:
                output = f"PASS: {test_name}"
                if verbose:
                    output += f"\nExpected output:\n{repr(expected_output)}"
                    output += f"\nActual output:\n{repr(actual_output)}"
            else:
                output = f"FAIL: {test_name}"
                output += f"\nExpected output:\n{repr(expected_output)}"
                output += f"\nActual output:\n{repr(actual_output)}"
                if result_stderr:
                    output += f"\nStderr:\n{result_stderr}"
        
        return success, output
        
    except subprocess.TimeoutExpired:
        return False, f"TIMEOUT: {test_name} exceeded {timeout} seconds"
    except Exception as e:
        return False, f"Error running {test_name}: {str(e)}"




def run_all_tests(shell_path="./minibash", verbose=False, point_system=None, with_valgrind=False):
    """
    Run all discovered tests with the given shell.
    
    Args:
        shell_path: Path to the shell executable to test
        verbose: Whether to show verbose output
        point_system: PointSystem instance for scoring
        with_valgrind: Whether to also run valgrind memory leak checking
    
    Returns:
        Tuple of (success: bool, output: str, results: dict, point_system: PointSystem)
    """
    script_dir = Path(__file__).resolve().parent
    py_tests = discover_tests(script_dir)
    sh_tests = discover_sh_tests(script_dir)
    
    # Initialize point system if not provided
    if point_system is None:
        point_system = PointSystem()
        point_system.distribute_points(
            sh_tests.get('basic', {}), 
            sh_tests.get('advanced', {}), 
            py_tests
        )
    
    # Count total tests for progress tracking
    total_tests = len(py_tests)
    for category_tests in sh_tests.values():
        total_tests += len(category_tests)
    
    all_output = []
    results = {}
    all_success = True
    current_test = 0
    start_time = time.time()
    
    # Print unified table header (only in non-verbose mode)
    if not verbose:
        table_header = create_table_header()
        print(f"\n{table_header}")
        all_output.append(table_header)
    else:
        print(f"\nRunning {total_tests} tests in verbose mode...\n")
    
    # Run Python tests
    if py_tests:
        print_section_header("Python Tests", verbose, all_output, add_top_separator=False)
        
        for test_name, (script_path, reg_path) in py_tests.items():
            current_test += 1
            
            # Run the functional test first
            success, output = run_test(test_name, script_path, shell_path, verbose, False)
            
            # Check valgrind if enabled
            valgrind_failed = False
            if with_valgrind:
                _, valgrind_output = run_test(test_name, script_path, shell_path, verbose, True)
                no_memory_leaks = check_valgrind_for_leaks(valgrind_output)
                point_system.record_valgrind_result(test_name, no_memory_leaks)
                valgrind_failed = not no_memory_leaks
            
            # Display the test result with valgrind status
            def dummy_runner(*args):
                return success, output
            
            _, _ = execute_and_display_test(
                test_name, dummy_runner, 
                (),  # No args needed for dummy runner
                point_system, current_test, total_tests, start_time, verbose, all_output,
                valgrind=with_valgrind, valgrind_failed=valgrind_failed
            )
            
            results[test_name] = success
            if not success:
                all_success = False
    
    # Run shell script tests
    for category in ['basic', 'advanced']:
        category_tests = sh_tests.get(category, {})
        if category_tests:
            print_section_header(f"{category.title()} Tests", verbose, all_output)
            
            # Sort tests by name for consistent output
            for test_name in sorted(category_tests.keys()):
                current_test += 1
                script_path, expected_path = category_tests[test_name]
                
                # Run the functional test first
                success, output = run_sh_test(test_name, script_path, expected_path, shell_path, verbose, False)
                
                # Check valgrind if enabled
                valgrind_failed = False
                if with_valgrind:
                    _, valgrind_output = run_valgrind_on_shell(script_path, shell_path)
                    no_memory_leaks = check_valgrind_for_leaks(valgrind_output)
                    point_system.record_valgrind_result(test_name, no_memory_leaks)
                    valgrind_failed = not no_memory_leaks
                
                # Display the test result with valgrind status
                def dummy_runner(*args):
                    return success, output
                
                _, _ = execute_and_display_test(
                    test_name, dummy_runner,
                    (),  # No args needed for dummy runner
                    point_system, current_test, total_tests, start_time, verbose, all_output,
                    valgrind=with_valgrind, valgrind_failed=valgrind_failed
                )
                
                results[f"{category}_{test_name}"] = success
                if not success:
                    all_success = False
    
    # Check if any tests were found
    if not py_tests and not any(sh_tests.values()):
        return False, "No tests discovered", {}, point_system
    
    # Evaluate valgrind results if valgrind was run
    if with_valgrind:
        point_system.evaluate_valgrind_results()
    
    print_score_summary(point_system, verbose, all_output)
    
    # Show completion message
    if total_tests > 0:
        elapsed_time = time.time() - start_time
        completion_msg = f"✓ Completed {total_tests} tests in {elapsed_time:.1f}s" + "\n"
        print(completion_msg)
    
    # Clean up core.die files generated by crash tests
    cleanup_core_files(script_dir)
    
    return all_success, '\n'.join(all_output), results, point_system


def run_shell_tests_category(category, category_tests, shell_path="./minibash", verbose=False, point_system=None, with_valgrind=False):
    """
    Run shell script tests for a specific category.
    
    Args:
        category: Category name ('basic' or 'advanced')
        category_tests: Dict of test_name -> (script_path, out_path)
        shell_path: Path to the shell executable to test
        verbose: Whether to show verbose output
        point_system: PointSystem instance for scoring
    
    Returns:
        Tuple of (success: bool, output: str, point_system: PointSystem)
    """
    # Initialize point system if not provided
    if point_system is None:
        point_system = PointSystem()
        if category == 'basic':
            point_system.distribute_points(category_tests, {}, {})
        else:
            point_system.distribute_points({}, category_tests, {})
    
    all_output = []
    all_success = True
    total_tests = len(category_tests)
    current_test = 0
    start_time = time.time()
    
    if not verbose:
        # Print unified table header
        table_header = create_table_header()
        print(f"\n{table_header}")
        all_output.append(table_header)
    else:
        print(f"\nRunning {total_tests} {category} tests in verbose mode...\n")
    
    print_section_header(f"{category.title()} Tests", verbose, all_output)
    
    for test_name in sorted(category_tests.keys()):
        current_test += 1
        script_path, expected_path = category_tests[test_name]
        
        # Run the functional test first
        success, output = run_sh_test(test_name, script_path, expected_path, shell_path, verbose, False)
        
        # Check valgrind if enabled
        valgrind_failed = False
        if with_valgrind:
            _, valgrind_output = run_valgrind_on_shell(script_path, shell_path)
            no_memory_leaks = check_valgrind_for_leaks(valgrind_output)
            point_system.record_valgrind_result(test_name, no_memory_leaks)
            valgrind_failed = not no_memory_leaks
        
        # Display the test result with valgrind status
        def dummy_runner(*args):
            return success, output
        
        _, _ = execute_and_display_test(
            test_name, dummy_runner,
            (),  # No args needed for dummy runner
            point_system, current_test, total_tests, start_time, verbose, all_output,
            valgrind=with_valgrind, valgrind_failed=valgrind_failed
        )
        
        if not success:
            all_success = False
    
    # Evaluate valgrind results if valgrind was run
    if with_valgrind:
        point_system.evaluate_valgrind_results()
    
    print_score_summary(point_system, verbose, all_output)
    
    # Show completion message
    if total_tests > 0:
        elapsed_time = time.time() - start_time
        completion_msg = f"✓ Completed {total_tests} {category} tests in {elapsed_time:.1f}s" + "\n"
        print(completion_msg)
    
    # Clean up core.die files generated by crash tests
    script_dir = Path(__file__).resolve().parent
    cleanup_core_files(script_dir)
    
    return all_success, '\n'.join(all_output), point_system


def run_python_tests_only(py_tests, shell_path="./minibash", verbose=False, point_system=None):
    """
    Run only Python tests.
    
    Args:
        py_tests: Dict of test_name -> (script_path, reg_path)
        shell_path: Path to the shell executable to test
        verbose: Whether to show verbose output
        point_system: PointSystem instance for scoring
    
    Returns:
        Tuple of (success: bool, output: str, point_system: PointSystem)
    """
    # Initialize point system if not provided
    if point_system is None:
        point_system = PointSystem()
        point_system.distribute_points({}, {}, py_tests)
    
    all_output = []
    all_success = True
    total_tests = len(py_tests)
    current_test = 0
    start_time = time.time()
    
    if not verbose:
        # Print unified table header
        table_header = create_table_header()
        print(f"\n{table_header}")
        all_output.append(table_header)
    else:
        print(f"\nRunning {total_tests} python tests in verbose mode...\n")
    
    print_section_header("Python Tests", verbose, all_output)
    
    for test_name, (script_path, reg_path) in py_tests.items():
        current_test += 1
        
        success, output = execute_and_display_test(
            test_name, run_test,
            (test_name, script_path, shell_path, verbose, False),  # False for valgrind
            point_system, current_test, total_tests, start_time, verbose, all_output,
            valgrind=False, valgrind_failed=False
        )
        
        if not success:
            all_success = False
    
    print_score_summary(point_system, verbose, all_output)
    
    # Show completion message
    if total_tests > 0:
        elapsed_time = time.time() - start_time
        completion_msg = f"✓ Completed {total_tests} python tests in {elapsed_time:.1f}s" + "\n"
        print(completion_msg)
    
    # Clean up core.die files generated by crash tests
    script_dir = Path(__file__).resolve().parent
    cleanup_core_files(script_dir)
    
    return all_success, '\n'.join(all_output), point_system


def run_three_phase_tests(shell_path="./minibash", verbose=False, with_valgrind=True):
    """
    Run tests in three phases:
    1. Basic tests without valgrind
    2. Advanced tests without valgrind  
    3. All tests with valgrind (if with_valgrind=True)
    
    Args:
        shell_path: Path to the shell executable to test
        verbose: Whether to show verbose output
        with_valgrind: Whether to run the valgrind phase
    
    Returns:
        Tuple of (overall_success: bool, combined_output: str, final_point_system: PointSystem)
    """
    script_dir = Path(__file__).resolve().parent
    py_tests = discover_tests(script_dir)
    sh_tests = discover_sh_tests(script_dir)
    
    # Initialize overall point system
    overall_point_system = PointSystem()
    overall_point_system.distribute_points(
        sh_tests.get('basic', {}), 
        sh_tests.get('advanced', {}), 
        py_tests
    )
    if with_valgrind:
        overall_point_system.add_valgrind_test()
    
    all_output = []
    overall_success = True
    phase_results = {}
    
    print(f"\n{'='*70}")
    print("MINIBASH TEST SUITE - THREE PHASE EXECUTION")
    print(f"{'='*70}")
    
    # Phase 1: Basic tests without valgrind
    if sh_tests.get('basic'):
        print(f"\n{'='*70}")
        print("PHASE 1: Basic Tests (Functional)")
        print(f"{'='*70}")
        
        basic_point_system = PointSystem.create_for_category(
            'basic', 
            sh_tests.get('basic', {}), 
            sh_tests.get('advanced', {}), 
            py_tests,
            include_valgrind=False
        )
        
        success, output, _ = run_shell_tests_category(
            'basic', sh_tests['basic'], shell_path, verbose, basic_point_system, False
        )
        
        phase_results['basic_functional'] = success
        all_output.append(f"Phase 1 - Basic Tests (Functional):\n{output}")
        if not success:
            overall_success = False
        
        # Record basic test results in overall system
        for test_name in sh_tests['basic']:
            overall_point_system.record_result(test_name, basic_point_system.results.get(test_name, False))
    
    # Phase 2: Advanced tests without valgrind  
    if sh_tests.get('advanced'):
        print(f"\n{'='*70}")
        print("PHASE 2: Advanced Tests (Functional)")
        print(f"{'='*70}")
        
        advanced_point_system = PointSystem.create_for_category(
            'advanced', 
            sh_tests.get('basic', {}), 
            sh_tests.get('advanced', {}), 
            py_tests,
            include_valgrind=False
        )
        
        success, output, _ = run_shell_tests_category(
            'advanced', sh_tests['advanced'], shell_path, verbose, advanced_point_system, False
        )
        
        phase_results['advanced_functional'] = success
        all_output.append(f"Phase 2 - Advanced Tests (Functional):\n{output}")
        if not success:
            overall_success = False
            
        # Record advanced test results in overall system
        for test_name in sh_tests['advanced']:
            overall_point_system.record_result(test_name, advanced_point_system.results.get(test_name, False))
    
    # Phase 3: Python tests without valgrind
    if py_tests:
        print(f"\n{'='*70}")
        print("PHASE 2.5: Python Tests (Functional)")
        print(f"{'='*70}")
        
        python_point_system = PointSystem.create_for_category(
            'python', 
            sh_tests.get('basic', {}), 
            sh_tests.get('advanced', {}), 
            py_tests,
            include_valgrind=False
        )
        
        success, output, _ = run_python_tests_only(py_tests, shell_path, verbose, python_point_system)
        
        phase_results['python_functional'] = success
        all_output.append(f"Phase 2.5 - Python Tests (Functional):\n{output}")
        if not success:
            overall_success = False
            
        # Record python test results in overall system
        for test_name in py_tests:
            overall_point_system.record_result(test_name, python_point_system.results.get(test_name, False))
    
    # Phase 3: All tests with valgrind (if enabled)
    if with_valgrind:
        print(f"\n{'='*70}")
        print("PHASE 3: Memory Safety Tests (Valgrind)")
        print(f"{'='*70}")
        
        valgrind_point_system = PointSystem()
        valgrind_point_system.distribute_points(
            sh_tests.get('basic', {}), 
            sh_tests.get('advanced', {}), 
            py_tests
        )
        valgrind_point_system.add_valgrind_test()
        
        success, output, results, _ = run_all_tests(shell_path, verbose, valgrind_point_system, True)
        
        phase_results['valgrind'] = success
        all_output.append(f"Phase 3 - Memory Safety Tests (Valgrind):\n{output}")
        
        # Record valgrind results in overall system
        for test_name, valgrind_result in valgrind_point_system.valgrind_results.items():
            overall_point_system.record_valgrind_result(test_name, valgrind_result)
        
        # Evaluate valgrind results
        overall_point_system.evaluate_valgrind_results()
    else:
        print(f"\n{'='*70}")
        print("PHASE 3: Memory Safety Tests (Valgrind) - SKIPPED")
        print(f"{'='*70}")
        print("Valgrind testing skipped (--no-valgrind flag used)")
        all_output.append("Phase 3 - Memory Safety Tests (Valgrind): SKIPPED")
    
    # Final summary
    print(f"\n{'='*70}")
    print("FINAL SUMMARY")
    print(f"{'='*70}")
    
    # Print phase results
    print("Phase Results:")
    if 'basic_functional' in phase_results:
        status = "✓ PASS" if phase_results['basic_functional'] else "✗ FAIL"
        print(f"  Basic Tests (Functional): {status}")
    
    if 'advanced_functional' in phase_results:
        status = "✓ PASS" if phase_results['advanced_functional'] else "✗ FAIL"
        print(f"  Advanced Tests (Functional): {status}")
        
    if 'python_functional' in phase_results:
        status = "✓ PASS" if phase_results['python_functional'] else "✗ FAIL"
        print(f"  Python Tests (Functional): {status}")
    
    if with_valgrind:
        if 'valgrind' in phase_results:
            valgrind_earned, valgrind_total = overall_point_system.get_score('valgrind')
            if valgrind_total > 0:
                percentage = (valgrind_earned / valgrind_total) * 100
                print(f"  Memory Safety (Valgrind): {valgrind_earned}/{valgrind_total} ({percentage:.1f}%)")
            else:
                print(f"  Memory Safety (Valgrind): No tests run")
    else:
        print("  Memory Safety (Valgrind): NOT TESTED")
    
    # Print overall score
    print("\nOverall Score:")
    for category in ['basic', 'advanced', 'python', 'valgrind']:
        earned, total = overall_point_system.get_score(category)
        if total > 0:
            percentage = (earned / total) * 100
            print(f"  {category.title()}: {earned}/{total} ({percentage:.1f}%)")
    
    earned, total = overall_point_system.get_score()
    percentage = (earned / total) * 100 if total > 0 else 0
    print(f"  TOTAL: {earned}/{total} ({percentage:.1f}%)")
    
    print(f"{'='*70}")
    
    # Clean up core.die files generated by crash tests
    cleanup_core_files(script_dir)
    
    return overall_success, '\n'.join(all_output), overall_point_system


def main():
    """Main function for standalone usage."""
    import argparse
    
    parser = argparse.ArgumentParser(
        description="Generic minibash driver for running test scripts",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python3 minibash_driver.py --shell ./minibash              # Default: 3-phase execution (basic, advanced, valgrind)
  python3 minibash_driver.py --shell ./minibash --no-valgrind # Skip valgrind phase
  python3 minibash_driver.py --test echo_test --shell ./minibash --verbose
  python3 minibash_driver.py --test 001-comment --shell ./minibash
  python3 minibash_driver.py -b --shell ./minibash           # Only basic tests
  python3 minibash_driver.py -a --shell ./minibash           # Only advanced tests
  python3 minibash_driver.py --valgrind --shell ./minibash   # All tests with valgrind (legacy mode)
  python3 minibash_driver.py --list-tests
        """
    )
    
    parser.add_argument("--shell", default="./minibash", help="Path to shell executable")
    parser.add_argument("--test", help="Run specific test (e.g., 'echo_test' or '001-comment')")
    parser.add_argument("-b", "--basic", action="store_true", help="Run only basic shell script tests (.sh/.out)")
    parser.add_argument("-a", "--advanced", action="store_true", help="Run only advanced shell script tests (.sh/.out)")
    parser.add_argument("--python-only", action="store_true", help="Run only Python tests (.py/.reg)")
    parser.add_argument("--valgrind", action="store_true", help="Run all tests with valgrind memory leak checking")
    parser.add_argument("--no-valgrind", action="store_true", help="Skip valgrind testing in default mode")
    parser.add_argument("--list-tests", action="store_true", help="List available tests")
    parser.add_argument("--verbose", "-v", action="store_true", help="Verbose output")
    
    # Point system configuration
    # parser.add_argument("--total-points", type=int, default=100, help="Total points available (default: 100)")
    # parser.add_argument("--basic-ratio", type=float, default=0.7, help="Ratio of points for basic tests (0.0-1.0, default: 0.7)")
    
    args = parser.parse_args()
    
    # Validate mutually exclusive arguments
    if args.valgrind and args.no_valgrind:
        print("Error: --valgrind and --no-valgrind are mutually exclusive")
        sys.exit(1)
    
    # Validate point system arguments
    # if args.basic_ratio < 0.0 or args.basic_ratio > 1.0:
    #     print("Error: --basic-ratio must be between 0.0 and 1.0")
    #     sys.exit(1)
    
    script_dir = Path(__file__).resolve().parent
    py_tests = discover_tests(script_dir)
    sh_tests = discover_sh_tests(script_dir)
    
    point_system = PointSystem()
    point_system.distribute_points(
        sh_tests.get('basic', {}), 
        sh_tests.get('advanced', {}), 
        py_tests
    )
    # Add valgrind test configuration to show in scoring
    # (Note: valgrind only enabled when --valgrind is used)
    point_system.add_valgrind_test()
    
    if args.list_tests:
        print("Available Python tests (.py/.reg):")
        for test_name in sorted(py_tests.keys()):
            if test_name in point_system.test_configs:
                points = point_system.test_configs[test_name].points
                print(f"  {test_name} ({points} pts)")
            else:
                print(f"  {test_name}")
        
        print("\nAvailable shell script tests (.sh/.out or .sh/.reg):")
        for category in ['basic', 'advanced']:
            category_tests = sh_tests.get(category, {})
            if category_tests:
                print(f"  {category.title()}:")
                for test_name in sorted(category_tests.keys()):
                    if test_name in point_system.test_configs:
                        points = point_system.test_configs[test_name].points
                        print(f"    {test_name} ({points} pts)")
                    else:
                        print(f"    {test_name}")
        
        print("\n" + point_system.get_summary())
        return
    
    if args.test:
        # Run specific test
        test_found = False
        
        # Check Python tests
        if args.test in py_tests:
            script_path, reg_path = py_tests[args.test]
            print(f"Running Python test: {args.test}")
            print(f"Script: {script_path}")
            print(f"Template: {reg_path}")
            
            success, output = run_test(args.test, script_path, args.shell, args.verbose)
            
            # Add point information if available
            if args.test in point_system.test_configs:
                points = point_system.test_configs[args.test].points
                earned = points if success else 0
                # Pad output to 55 characters and add points in right column
                base_output = output.rstrip()
                padded_output = base_output.ljust(55)
                point_status = f"{earned}/{points} pts"
                output = padded_output + point_status
            
            print(output)
            
            # Clean up core.die files generated by crash tests
            cleanup_core_files(script_dir)
            
            sys.exit(0 if success else 1)
        
        # Check shell script tests
        for category in ['basic', 'advanced']:
            category_tests = sh_tests.get(category, {})
            if args.test in category_tests:
                script_path, expected_path = category_tests[args.test]
                print(f"Running shell script test ({category}): {args.test}")
                print(f"Script: {script_path}")
                print(f"Expected: {expected_path}")
                
                success, output = run_sh_test(args.test, script_path, expected_path, args.shell, args.verbose)
                
                # Check valgrind if requested
                if args.valgrind:
                    _, valgrind_output = run_valgrind_on_shell(script_path, args.shell)
                    no_memory_leaks = check_valgrind_for_leaks(valgrind_output)
                    if not no_memory_leaks and success:
                        output = output.replace("PASS:", "PASS (valgrind failed):")
                
                # Add point information if available
                if args.test in point_system.test_configs:
                    points = point_system.test_configs[args.test].points
                    earned = points if success else 0
                    # Pad output to 55 characters and add points in right column
                    base_output = output.rstrip()
                    padded_output = base_output.ljust(55)
                    point_status = f"{earned}/{points} pts"
                    output = padded_output + point_status
                
                print(output)
                
                # Clean up core.die files generated by crash tests
                cleanup_core_files(script_dir)
                
                sys.exit(0 if success else 1)
        
        print(f"Error: Test '{args.test}' not found.")
        print("Available Python tests:", ", ".join(py_tests.keys()))
        all_sh_tests = []
        for category_tests in sh_tests.values():
            all_sh_tests.extend(category_tests.keys())
        print("Available shell script tests:", ", ".join(sorted(all_sh_tests)))
        sys.exit(1)
    
    elif args.basic:
        # Run only basic shell script tests
        if not sh_tests.get('basic'):
            print("No basic shell script tests found.")
            sys.exit(1)
        
        # Create category-specific point system with correct proportional points
        basic_point_system = PointSystem.create_for_category(
            'basic', 
            sh_tests.get('basic', {}), 
            sh_tests.get('advanced', {}), 
            py_tests,
            include_valgrind=args.valgrind
        )
        
        success, output, _ = run_shell_tests_category('basic', sh_tests['basic'], args.shell, args.verbose, basic_point_system, args.valgrind)
        sys.exit(0 if success else 1)
    
    elif args.advanced:
        # Run only advanced shell script tests
        if not sh_tests.get('advanced'):
            print("No advanced shell script tests found.")
            sys.exit(1)
        
        # Create category-specific point system with correct proportional points
        advanced_point_system = PointSystem.create_for_category(
            'advanced', 
            sh_tests.get('basic', {}), 
            sh_tests.get('advanced', {}), 
            py_tests,
            include_valgrind=args.valgrind
        )
        
        success, output, _ = run_shell_tests_category('advanced', sh_tests['advanced'], args.shell, args.verbose, advanced_point_system, args.valgrind)
        sys.exit(0 if success else 1)
    
    elif args.python_only:
        # Run only Python tests
        if not py_tests:
            print("No Python tests found.")
            sys.exit(1)
        
        # Create category-specific point system with correct proportional points
        python_point_system = PointSystem.create_for_category(
            'python', 
            sh_tests.get('basic', {}), 
            sh_tests.get('advanced', {}), 
            py_tests,
            include_valgrind=False  # Python tests don't typically use valgrind
        )
        
        success, output, _ = run_python_tests_only(py_tests, args.shell, args.verbose, python_point_system)
        sys.exit(0 if success else 1)
    
    else:
        # Run all tests (default behavior: three-phase execution)
        # Determine whether to run valgrind based on flags
        run_valgrind = not args.no_valgrind and not args.valgrind
        if args.valgrind:
            # If --valgrind is specified, run old behavior for compatibility
            success, output, results, final_point_system = run_all_tests(args.shell, args.verbose, point_system, True)
        else:
            # New default behavior: three-phase execution
            success, output, final_point_system = run_three_phase_tests(args.shell, args.verbose, run_valgrind)
        sys.exit(0 if success else 1)


if __name__ == "__main__":
    main()
