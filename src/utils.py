"""
Utility functions for the adelic-bsd package
"""

import os


def get_safe_output_path(filename_or_dir, is_dir=False):
    """
    Get a safe path for file or directory output.
    
    Uses GITHUB_WORKSPACE when available (in GitHub Actions), otherwise uses
    the current working directory. This prevents permission errors when writing
    to restricted locations in CI/CD environments.
    
    Args:
        filename_or_dir: Filename or directory path (can be relative or absolute)
        is_dir: If True, ensures the directory is created
        
    Returns:
        str: Safe absolute path for the file or directory
        
    Examples:
        >>> # In GitHub Actions
        >>> get_safe_output_path('output.txt')
        '/home/runner/work/repo/repo/output.txt'
        
        >>> # Outside GitHub Actions
        >>> get_safe_output_path('output.txt')
        '/current/working/directory/output.txt'
        
        >>> # With absolute path
        >>> get_safe_output_path('/tmp/output.txt')
        '/tmp/output.txt'
    """
    # Get safe base directory
    safe_base = os.environ.get('GITHUB_WORKSPACE', os.getcwd())
    
    # If path is absolute, use it as-is; otherwise make it relative to safe_base
    if os.path.isabs(filename_or_dir):
        safe_path = filename_or_dir
    else:
        safe_path = os.path.join(safe_base, filename_or_dir)
    
    # Create directory if requested
    if is_dir:
        os.makedirs(safe_path, exist_ok=True)
    
    return safe_path
