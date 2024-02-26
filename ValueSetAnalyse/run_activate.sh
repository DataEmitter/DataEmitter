set -e

python_script="main.py"
directory_path="in/$1/P1P2"
output_directory="out/$1/P1P2_VSA"


function handle_error {
    local exit_code=$?
    local file_path=$1
    echo "Error occurred while running $python_script with input file: $file_path"
    echo "Files successfully processed:"
    echo "$processed_files"
    exit $exit_code
}


trap 'handle_error "$file_path"' ERR


processed_files=""

for file_path in "$directory_path"/*
do
    if [ -f "$file_path" ]; then
        file_name=$(basename "$file_path")
        output_file_path="$output_directory/$file_name"
        
        if [ -f "$output_file_path" ]; then
            echo "Skipping $python_script for input file: $file_path (output file already exists)"
            continue
        fi
        
        echo -e "Running $python_script with input file: $file_path\n"
        python3 "$python_script" "$file_path" 2>/dev/null
        echo -e "Finished running $python_script with input file: $file_path\n"
        
        processed_files+="\n$file_path"
    fi
done