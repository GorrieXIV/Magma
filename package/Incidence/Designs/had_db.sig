174,1
V,HadamardDB,3
S,HadamardDatabaseInformationEmpty,Produces an internal representation of a Hadamard database with no entries in it. Set the parameter Canonical to false if the database should store the original forms of matrices rather than the canonical ones,0,0,0,0,0,0,0,270,-38,-38,-38,-38,-38
S,HadamardDatabaseInformation,"Produces an internal representation of the Hadamard database for use by other intrinsics. Set the parameter Canonical to false if the entries in the database are not in canonical form (e.g., the skew database)",0,1,0,0,0,0,0,0,0,53,,270,-38,-38,-38,-38,-38
S,UpdateHadamardDatabase,Add new inequivalent matrices from S to the data in the given tuple. Set the parameter Canonical to true if these matrices are known to be in canonical form already,1,1,1,82,0,177,2,0,0,1,0,0,0,0,82,,1,1,270,,-38,-38,-38,-38,-38,-38
S,WriteHadamardDatabase,Creates new database files from the given data,0,2,0,0,1,0,0,1,1,270,,0,0,298,,-38,-38,-38,-38,-38,-38
S,WriteRawHadamardData,"Creates a loadable Magma file with the raw data for a database. This is useful when the stored entries are not in canonical form (i.e., the skew database), since the canonical information is stored in the raw data. WARNING: This will destroy the old contents of the file",0,2,0,0,1,0,0,0,0,270,,0,0,298,,-38,-38,-38,-38,-38,-38
