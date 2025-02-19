r'''
    Script to manage the results of almost commuting operators with the repository :git:`da_wilson`.

    This script have the functionalities to send the results to the :git:`da_wilson` from the results
    folder in the `dalgebra` package in the parent folders. This script can also be used to import
    the results from the repository (either locally or remotely), so once the package is installed
    (see Makefile in the parent folder), the results can be used in the `dalgebra` package, simplifying
    computations.

    This script can be split into two main functionalities:

    * `send`: send the result of the almost commuting operators to the repository. It receives one 
      argument "-folder" that is the folder where the `da_wilson` repository is located.
    * `import`: import the results of the almost commuting operators from the repository. It receives
      one optional argument "-folder" that is the folder where the `da_wilson` repository is located.
      If not provided, the results are imported from the remote repository (with default url values)
'''

import os
import shutil
import argparse
import tempfile
import subprocess
import sys
import re

sys.path.insert(0, "../..") # dalgebra is here

from dalgebra import dalgebra_folder, dalgebra_version

RESULTS_FOLDER = os.path.join(dalgebra_folder(), 'results', 'almost_commuting') 

def send_results(folder: str):
    print(f"### SENDING RESULTS TO REPOSITORY ###")
    ## Creating the path to the results and destination folders
    destination_folder = os.path.join(folder, 'data')
    if not os.path.exists(destination_folder):
        raise ValueError(f" !! Folder {destination_folder} does not exist.")
    
    ## Regex for the file names
    regex = re.compile(r'base_almost_commuting_wilson\((\d+),(\d+)\)\[\]_[\d\.]+.out')
    
    print(f" ++ Copying files from {RESULTS_FOLDER} to {destination_folder}")
    ## Copying files
    for filename in os.listdir(RESULTS_FOLDER):
        M = regex.match(filename)
        if M is not None:
            n, m = (int(el) for el in M.groups())
            full_file_name = os.path.join(RESULTS_FOLDER, filename)
            full_copied_name = os.path.join(destination_folder, filename)
            full_final_name = os.path.join(destination_folder, f"({n}_{m}).out")
            ## Copy and rename files (deleting previous versions)
            if os.path.isfile(full_file_name):
                if os.path.exists(full_final_name):
                    os.remove(full_final_name)
                shutil.copy(full_file_name, destination_folder)
                shutil.move(full_copied_name, full_final_name)
        else:
            print(f" !! File {filename} does not match the expected pattern.")
    print(f" ++ Results sent to {destination_folder}")
    print(f"### FINISHED SENDING RESULTS TO REPOSITORY ###")

def import_results(folder: str = None, version: str = None):
    print(f"### IMPORTING RESULT FILES ###")
    temporary = False
    try:
        if folder is None:
            temporary = True
            print(f" ++ Folder not provided. Importing from remote repository...")
            repo_url = "https://github.com/Antonio-JP/da_wilson.git"
            folder = tempfile.mkdtemp() # pathname for temporary folder
            subprocess.run(['git', 'clone', repo_url, folder], capture_output=True, check = True)
            print(f" ++ Cloned repository")

        if not os.path.exists(RESULTS_FOLDER):
            os.makedirs(RESULTS_FOLDER)

        source_folder = os.path.join(folder, 'data', 'sage')
        version = version if version is not None else dalgebra_version()

        ## Regex for the file names
        regex = re.compile(r'\((\d+)_(\d+)\).out')

        print(f" ++ Copying files from {source_folder} to {RESULTS_FOLDER}")
        for filename in os.listdir(source_folder):
            ## Creating the names for all the files to be used
            full_file_name = os.path.join(source_folder, filename)
            full_copied_name = os.path.join(RESULTS_FOLDER, filename)
            
            ## Checking if the original file matches the expected pattern
            M = regex.match(filename)
            if M is not None:
                (n,m) = (int(el) for el in M.groups())
                full_final_name = os.path.join(RESULTS_FOLDER, f"base_almost_commuting_wilson({n},{m})[]_{version}.out")
                if os.path.exists(full_final_name):
                    os.remove(full_final_name)
                shutil.copy(full_file_name, RESULTS_FOLDER)
                shutil.move(full_copied_name, full_final_name)
            else:
                print(f" !! File {filename} does not match the expected pattern.")

    except subprocess.CalledProcessError as e:
        print(f" -- Error cloning the repository: {e}")
    finally:
        if temporary:
            print(f" ++ Removing temporary files...")
            subprocess.run(['rm', '-rf', folder], check = True)

    print(f"### FINISHED IMPORT OF RESULT FILES ###")
    
        
if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Manage results of almost commuting operators.')
    subparsers = parser.add_subparsers(dest='command')

    send_parser = subparsers.add_parser('send', help='Send results to the repository')
    send_parser.add_argument('-folder', required=True, help='Folder where the da_wilson repository is located')

    import_parser = subparsers.add_parser('import', help='Import results from the repository')
    import_parser.add_argument('-folder', help='Folder where the da_wilson repository is located')
    import_parser.add_argument('-version', help='Folder where the da_wilson repository is located')

    args = parser.parse_args()

    if args.command == 'send':
        send_results(args.folder)
    elif args.command == 'import':
        import_results(args.folder, args.version)
    