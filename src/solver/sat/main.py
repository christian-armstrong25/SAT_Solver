import sys
from pathlib import Path
from solver.sat.timer import Timer
from solver.sat.dimacs_parser import DimacsParser

def main():
    if len(sys.argv) < 2:
        print("Usage: python main.py <cnf file>")
        return
    
    input_file = sys.argv[1]
    filename = Path(input_file).name
    
    watch = Timer()
    watch.start()
    
    try:
        instance = DimacsParser.parse_cnf_file(input_file)
        print(instance)
        
        watch.stop()
        print(f'{{"Instance": "{filename}", "Time": {watch.get_time():.2f}, "Result": "--"}}')
    
    except Exception as e:
        print(f"Error: {str(e)}")

if __name__ == "__main__":
    main() 