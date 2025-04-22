default: result.hoa
rabin_0b0_0b0.hoa: stable_0b0.hoa 
	autfilt --gra -o rabin_0b0_0b0.hoa -F stable_0b0.hoa 
c3_0b0_0b1.hoa: safety_0b0_0.hoa 
	autfilt --coBuchi -o c3_0b0_0b1.hoa -F safety_0b0_0.hoa 
rabin_0b0_0b1.hoa: stable_0b0.hoa c3_0b0_0b1.hoa 
	autfilt --gra -o rabin_0b0_0b1.hoa -F stable_0b0.hoa --product=c3_0b0_0b1.hoa
result.hoa: rabin_0b0_0b0.hoa rabin_0b0_0b1.hoa 
	autfilt --gra --generic --complete -D -o result.hoa -F rabin_0b0_0b0.hoa --product-or=rabin_0b0_0b1.hoa 
