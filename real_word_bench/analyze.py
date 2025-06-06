import re
import sys

def extract_and_csv_total_times() -> str:
    """
    Reads 'time' command outputs from standard input, extracts 'total time' values,
    and returns them as a single-row CSV string.

    Returns:
        A string representing the extracted total times in a single-row CSV format.
    """
    total_times_in_seconds = []

    # Read lines from standard input until EOF
    for line in sys.stdin:
        # Regex to find the 'total' time.
        # It handles both 'X.YYY total' and 'MM:SS.ms total' formats.
        # Group 1: captures minutes if present (e.g., '1:')
        # Group 2: captures seconds and milliseconds (e.g., '00.91')
        match = re.search(r'(\d+:)?(\d+\.\d+) total', line)
        if match:
            minutes_str = match.group(1) # e.g., '1:' or None
            seconds_ms_str = match.group(2) # e.g., '00.91' or '26.298'

            total_seconds = 0.0
            if minutes_str:
                # Convert minutes to seconds if present
                minutes = int(minutes_str.strip(':'))
                total_seconds += minutes * 60

            # Add the seconds and milliseconds part
            total_seconds += float(seconds_ms_str)

            total_times_in_seconds.append(total_seconds)
        elif line.strip().lower().startswith('x'):
            total_times_in_seconds.append(-1)
    # Manually construct the CSV string
    csv_lines = []

    # Create header row
    headers = [f'Total_Time_{i+1}_Seconds' for i in range(len(total_times_in_seconds))]
    csv_lines.append(','.join(headers))

    # Create data row
    data_row = [str(time) for time in total_times_in_seconds]
    csv_lines.append(','.join(data_row))

    return '\n'.join(csv_lines)

if __name__ == "__main__":
    # Call the function to extract times from stdin and print the CSV result
    csv_result = extract_and_csv_total_times()
    print(csv_result)

extract_and_csv_total_times()
