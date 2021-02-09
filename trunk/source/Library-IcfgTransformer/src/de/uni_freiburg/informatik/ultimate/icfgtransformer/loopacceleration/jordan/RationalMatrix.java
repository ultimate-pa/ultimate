package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.jordan;

public class RationalMatrix {
	// Class for rational matrices
	// which consist of an integer matrix
	// and one common denominator for all entries.
	
	QuadraticMatrix int_matrix;
	int denominator;
	
	RationalMatrix(int M_denominator, QuadraticMatrix M) {
		// Constructor.
		
		denominator = M_denominator;
		int_matrix = M;
	}
	
	public static RationalMatrix inverse(final RationalMatrix M) {
		// Input: Rational Matrix M.
		// Returns the inverse of M using the inverse of the integer matrix.
		// Using: (c*M)^-1 = c^-1 * M ^-1.
		
		final int n = M.int_matrix.dimension;
		RationalMatrix M_inverse = QuadraticMatrix.inverse(M.int_matrix);
		myRational factor_inverse = new myRational(M.denominator, M_inverse.denominator);
		factor_inverse = myRational.reduce_fraction(factor_inverse);
		for (int i=0; i<n; i++) {
			for (int j=0; j<n; j++) {
				M.int_matrix.entries[i][j] = M.int_matrix.entries[i][j] * factor_inverse.numerator;
			}
		}
		M_inverse.denominator = factor_inverse.denominator;
		return M_inverse;
	}
}
