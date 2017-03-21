174,1
S,StringToBytes,Converts a string S to a sequence of bytes (integers in the range 0..255),0,1,0,0,0,0,0,0,0,298,,82,-38,-38,-38,-38,-38
S,BytesToString,Converts a sequence of bytes (integers in the range 0..255) to a string,1,0,1,82,0,148,1,0,0,0,0,0,0,0,82,,298,-38,-38,-38,-38,-38
S,BinaryToBytes,Converts a sequence S of binary values (integers in the range 0..1) to a sequence of bytes (integers in the range 0..255). The length of the sequence S must be divisible by 8,1,0,1,82,0,148,1,0,0,0,0,0,0,0,82,,82,-38,-38,-38,-38,-38
S,IsBase64Encoded,True iff the given string looks like base64 encoded data,0,1,0,0,0,0,0,0,0,298,,36,-38,-38,-38,-38,-38
S,Base64Encode,Encodes the sequence of bytes (integers in the range 0..255) using base64 encoding,1,0,1,82,0,148,1,0,0,0,0,0,0,0,82,,298,-38,-38,-38,-38,-38
S,Base64Encode,Encodes the string using base64 encoding,0,1,0,0,0,0,0,0,0,298,,298,-38,-38,-38,-38,-38
S,Base64EncodeFile,,0,1,0,0,0,0,0,0,0,298,,298,-38,-38,-38,-38,-38
S,Base64EncodeFile,Encodes the indicated file using base64 encoding,0,2,0,0,1,0,0,0,0,298,,0,0,298,,-38,-38,-38,-38,-38,-38
S,Base64Decode,Decodes the string using base64 decoding. The unencoded data is given as a sequence of bytes (integers in the range 0..255),0,1,0,0,0,0,0,0,0,298,,82,-38,-38,-38,-38,-38
S,Base64DecodeFile,Decodes the indicated file using base64 decoding. The unencoded data is given as a sequence of bytes (integers in the range 0..255),0,1,0,0,0,0,0,0,0,298,,82,-38,-38,-38,-38,-38
S,Base64DecodeFile,Decodes the indicated file using base64 decoding,0,2,0,0,1,0,0,0,0,298,,0,0,298,,-38,-38,-38,-38,-38,-38
