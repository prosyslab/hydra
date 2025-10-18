rm -r hydra-inputs
tar -xzvf hydra-inputs.tar.gz
rm -r hydra-outputs
mkdir -p hydra-outputs

echo "===== START ====="
find hydra-inputs -name '*.opt' | parallel \
  --bar --joblog run.log --timeout 3600 --j (nproc) \
  'cat {} | tee hydra-outputs/{/}.input | build/hydra > hydra-outputs/{/}.result 2> hydra-outputs/{/}.error'
# for input_file in hydra-inputs/*.opt
# 	echo $input_file
# 	set base_name (path basename $input_file)
# 	find hydra-inputs -name '*.opt' | parallel \
# 		--bar \
# 	  --joblog run.log \
# 		--timeout 3600 \
# 	  --j (nproc) \
# 			'cat {} | tee hydra-outputs/{/}.input | build/hydra > hydra-outputs/{/}.result 2> hydra-outputs/{/}.error'
# end
echo "===== DONE ====="

