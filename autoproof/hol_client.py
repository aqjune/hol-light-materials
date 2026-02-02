#!/usr/bin/env python3

"""
Python client for HOL Light Server2. Largely written by Kiro

Usage: python hol_client.py <server_address> <input.txt>
Example: python hol_client.py localhost:2012 input.txt
"""

import sys
import socket
import json


def escape_string(s):
    """
    Mimics OCaml's String.escaped function.
    Returns a string with special characters escaped.
    """
    result = []

    for char in s:
        code = ord(char)

        if char == '\\':
            result.append('\\\\')
        elif char == '"':
            result.append('\\"')
        elif char == '\n':
            result.append('\\n')
        elif char == '\t':
            result.append('\\t')
        elif char == '\r':
            result.append('\\r')
        elif char == '\b':
            result.append('\\b')
        elif code < 32 or code >= 127:
            # Format as \DDD where DDD is the decimal code (3 digits, zero-padded)
            result.append(f'\\{code:03d}')
        else:
            result.append(char)
    return ''.join(result)

def parse_server_message(line):
    """Parse a server message into (message_type, content)"""
    if ':' not in line:
        return None, line

    msg_type, content = line.split(':', 1)
    return msg_type, content

def read_response(sock_file, result):
    # Read response messages
    while True:
        line = sock_file.readline().strip()
        if not line:
            break

        msg_type, content = parse_server_message(line)

        if msg_type == 'stdout':
            result['stdout'].append(content)
        elif msg_type == 'stderr':
            result['stderr'].append(content)
        elif msg_type == 'result':
            result['result'] = content
            # After result, we're done
            break
        elif msg_type == 'rerror':
            result['error'] = content
            # After error, we're done
            break
        elif msg_type == 'ready':
            # Got ready again, we're done
            result['ready'].append(content)
            break

def send_command(host, port, command, timeout):
    """Send a command to the server and collect all responses"""
    result = {
        'info': [],
        'ready': [],
        'stdout': [],
        'stderr': [],
        'result': None,
        'error': None
    }

    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
        sock.settimeout(timeout)
        sock.connect((host, port))
        sock_file = sock.makefile('rw', encoding='utf-8', newline='\n')

        # Read initial messages (info and ready)
        while True:
            line = sock_file.readline().strip()
            if not line:
                break

            msg_type, content = parse_server_message(line)

            if msg_type == 'info':
                result['info'].append(content)
            elif msg_type == 'ready':
                result['ready'].append(content)
                # Server is ready, send the command
                escaped_cmd = escape_string(command)
                sock_file.write(escaped_cmd + '\n')
                sock_file.flush()
                break

        # Read response messages
        try:
            read_response(sock_file, result)
        except socket.timeout:
            print(f"Timeout: {timeout} sec.")
            sock_file.write("$interrupt\n")
        """
        read_response(sock_file, result)
        """
        sock_file.write('#quit\n')
        sock_file.flush()
        sock_file.close()

    return result


def main():
    if len(sys.argv) != 3:
        print("Usage: python hol_client.py <server_address> <input file>", file=sys.stderr)
        print("Example: python hol_client.py localhost:30000 input.txt", file=sys.stderr)
        sys.exit(1)

    server_address = sys.argv[1]
    command_file = sys.argv[2]
    with open(command_file, "r") as f:
        command = "".join(f.readlines()).strip()
    timeout = 30 # seconds

    # Parse server address
    if ':' in server_address:
        host, port_str = server_address.rsplit(':', 1)
        port = int(port_str)
    else:
        print("Error: Server address must be in format host:port", file=sys.stderr)
        sys.exit(1)

    try:
        result = send_command(host, port, command, timeout)
        print(json.dumps(result, indent=2))
    except Exception as e:
        error_result = {
            'error': str(e),
            'info': [],
            'ready': [],
            'stdout': [],
            'stderr': [],
            'result': None
        }
        print(json.dumps(error_result, indent=2))
        sys.exit(1)


if __name__ == '__main__':
    main()
