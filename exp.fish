tar -xzvf hydra-inputs.tar.gz
rm -r hydra-outputs
mkdir -p hydra-outputs

for input_file in hydra-inputs/*.opt
	echo $input_file
	set base_name (path basename $input_file)
	timeout 1h cat $input_file | tee hydra-outputs/$base_name.input | build/hydra > hydra-outputs/$base_name.result 2> hydra-outputs/$base_name.error
end

