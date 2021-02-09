package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.jordan;

public class QuadraticMatrix {
	// Class for quadratic integer matrices.
	// Goal: compute Jordan normal form for matrices with eigenvalues only -1,0,1.
	
	// entries is an integer array of arrays representing the entries of the matrix.
	// dimension is an integer representing the number of rows/columns of the matrix.
			
	int dimension;
	int[][] entries = new int[dimension][dimension];
	
	public QuadraticMatrix(int[][] matrix_entries) {
		// Constructor.
		
		// Check if given array of arrays is quadratic.
		int number_of_rows = matrix_entries.length;
		for (int i=0; i<number_of_rows; i++) {
			if (number_of_rows != matrix_entries[i].length) {
				throw new AssertionError("Some matrix is not quadratic");
				// System.out.println("Some matrix is not quadratic!");
				// System.exit(0);
			}
		}
		
		// Set member variables.
		entries = matrix_entries;
		dimension = number_of_rows;
	}
	
	public static QuadraticMatrix identity_matrix(final int n) {
		// Constructs the identity matrix of dimension n.
		
		int[][] identity_entries = new int[n][n];
		for (int i=0; i<n; i++) {
			for (int j=0; j<n; j++) {
				if (i==j) {
					identity_entries[i][j] = 1;
				}
				else { identity_entries[i][j] = 0; }
			}
		}
		final QuadraticMatrix E = new QuadraticMatrix(identity_entries);
		return E;
	}
	
	public static QuadraticMatrix zero_matrix(final int n) {
		// Constructs the zero matrix of dimension n.
		
		int[][] identity_entries = new int[n][n];
		for (int i=0; i<n; i++) {
			for (int j=0; j<n; j++) {
				identity_entries[i][j] = 0;
			}
		}
		final QuadraticMatrix E = new QuadraticMatrix(identity_entries);
		return E;
	}
	
	private static QuadraticMatrix copy_matrix(final QuadraticMatrix M) {
		// Copies the matrix M.
		// Used to make sure to not change the matrix applying functions.
		
		final int n = M.dimension;
		int[][] copied_entries = new int[n][n];
		for (int i=0; i<n; i++) {
			for (int j=0; j<n; j++) {
				copied_entries[i][j] = M.entries[i][j];
			}
		}
		final QuadraticMatrix M_copied = new QuadraticMatrix(copied_entries);
		return M_copied;
	}
	
	private static QuadraticMatrix addition(final QuadraticMatrix M1, final QuadraticMatrix M2) {
		// Input: two quadratic matrices M1 and M2.
		// Returns matrix addition of M1 and M2
		// if the matrices are of the same dimension.
		// Fails otherwise.
		
		// Check if both matrices are of the same dimension.
		if (M1.dimension != M2.dimension) {
			throw new AssertionError("Some matrices for addition are not of the same dimension.");
		}
		final int n = M1.dimension;
		int[][] sum_entries = new int[n][n];
		QuadraticMatrix Sum = new QuadraticMatrix(sum_entries);
		
		// Compute usual matrix addition.
		for (int i=0; i<n; i++) {
			for (int j=0; j<n; j++) {
				Sum.entries[i][j] = M1.entries[i][j] + M2.entries[i][j];
			}
		}
		return Sum;
	}
	
	private static QuadraticMatrix scalar_multiplication(final int a, final QuadraticMatrix M) {
		// Input: an integer scalar and a quadratic matrix.
		// Returns Scmult = a * M, the usual scalar multiplication.
		
		final int n = M.dimension;
		int[][] scmult_entries = new int[n][n];
		for (int i=0; i<n; i++) {
			for (int j=0; j<n; j++) {
				scmult_entries[i][j] = a * M.entries[i][j];
			}
		}
		final QuadraticMatrix Scmult = new QuadraticMatrix(scmult_entries);
		return Scmult;
	}
	
	private static QuadraticMatrix multiplication(final QuadraticMatrix M1, final QuadraticMatrix M2) {
		// Input: two quadratic matrices.
		// Returns Product = M1 * M2 (matrix multiplication)
		// if the matrices are of the same dimension.
		// Fails otherwise.
		
		// Check if both matrices have the same dimension.
		if (M1.dimension != M2.dimension) {
			throw new AssertionError("Some matrices for multiplication are not of the same dimension");
		}
		
		// Compute usual matrix multiplication.
		final int n = M1.dimension;
		int[][] product_entries = new int[n][n];
		for (int i=0; i<n; i++) {
			for (int k=0; k<n; k++) {
				for (int j=0;j<n; j++) {
					product_entries[i][k] = product_entries[i][k] + (M1.entries[i][j] * M2.entries[j][k]);
				}
			}
		}
		final QuadraticMatrix Product = new QuadraticMatrix(product_entries);
		return Product;
	}
	
	private static QuadraticMatrix power(final QuadraticMatrix M, final int s) {
		// Input: a quadratic matrix M and an integer s.
		// Returns Power = M^s (matrix power).
		
		final int n = M.dimension;
		if (s == 0) { return identity_matrix(n); }
		if (s == 1) { return M; }
		QuadraticMatrix Power = copy_matrix(M);
		for (int i=2; i<=s; i++) {
			Power = multiplication(Power, M);
		}
		return Power;
	}
	
	private int det() {
		// Returns the determinant of a quadratic matrix M.
		// Recursive computation using Laplace expansion.
		
		final int n = dimension;
		// Base cases.
		// 1x1 matrices.
		if (n == 1) {
			return entries[0][0];
		}
		
		// 2x2 matrices.
		if (n == 1) {
			return entries[0][0] * entries[1][1] - entries[0][1] * entries[1][0];
		}
		
		// 3x3 matrices.
		if (n == 3) {
			return entries[0][0] * entries[1][1] * entries[2][2]
					+ entries[0][1] * entries[1][2] * entries[2][0]
					+ entries[0][2] * entries[1][0] * entries[2][1]
					- entries[2][0] * entries[1][1] * entries[0][2]
					- entries[2][1] * entries[1][2] * entries[0][0]
					- entries[2][2] * entries[1][0] * entries[0][1];
		}
		
		// Recursive case: nxn matrices for n>3.
		int det = 0;
		// Delete last row and one column after the other.
		for (int k=0; k<n; k++ ) {
			int[][] K_tmp = new int[n-1][n-1];
			for (int i=0; i<n-1; i++) {
				for (int j=0; j<k; j++) {
					K_tmp[i][j] = entries[i][j];
				}
				for (int j=k+1; j<n; j++) {
					K_tmp[i][j-1] = entries[i][j];
				}
			}
			QuadraticMatrix K = new QuadraticMatrix(K_tmp);
			if ((n+k-1) % 2 == 0) {
				det = det + entries[n-1][k] * K.det();
			}
			else { det = det - entries[n-1][k] * K.det(); }
		}
		return det;
	}
	
	public static RationalMatrix inverse(final QuadraticMatrix M) {
		// Input: a quadratic integer matrix M.
		// Computes inverse of a quadratic matrix M.
		// Inverse is a rational matrix and
		// consists of a quadratic integer matrix
		// and a main denominator for all the entries.
		
		// Check if matrix is invertible. If not, stop.
		final int n = M.dimension;
		if (M.det() == 0) {
			throw new AssertionError("Matrix is not invertible");
		}
		
		// For every column of the matrix M
		// construct LES for inverse matrix: M*M^-1 = E.
		int[][] inverse_entries = new int[n][n];
		QuadraticMatrix inverse_int = new QuadraticMatrix(inverse_entries);
		RationalMatrix inverse = new RationalMatrix(1,inverse_int);
		for (int k=0; k<n; k++) {
			int[][] les_entries = new int[n+1][n+1];
			for (int i=0; i<n; i++) {
				for (int j=0; j<n; j++) {
					les_entries[i][j] = M.entries[i][j];
				}
			}
			for (int i=0; i<n; i++) {
				if (i == k) { les_entries[i][n] = 1; }
				else {les_entries[i][n] = 0; }
			}
			for (int j=0; j<n; j++) {
				les_entries[n][j] = 0;
			}
			les_entries[n][n] = 1;
			QuadraticMatrix LES = new QuadraticMatrix(les_entries);
			// Solve LES using gaussian elimination and backwards substitution
			// For every column of the inverse matrix.
			
			QuadraticMatrix GLES = gauss_elimination(LES);
			myRational[] xk = backwards_substitution(GLES, 1);
			add_vector_to_matrix(inverse, k, xk);
		}
		return inverse;
	}
	
	private boolean[] small_eigenvalues() {
		// Checks if -1,0,1 are eigenvalues of a quadratic matrix.
		// Returns a boolean array of size 3
		// where the i-th entry is true iff i-1 is an eigenvalue of the matrix.
		
		boolean[] eigenvalues = new boolean[3];
		for (int i=0; i<3; i++) {
			eigenvalues[i] = false;
		}
		// Check if i is an eigenvalue for i = -1,0,1
		// By checking if i is a zero of the characteristic polynomial.
		final int n = dimension;
		final QuadraticMatrix E = identity_matrix(n);
		for (int i=-1; i<2; i++) {
			if ((addition(this, scalar_multiplication(-i, E))).det() == 0) {
				eigenvalues[i+1] = true;
			}
		}
		return eigenvalues;
	}
	
	private void swap_rows(final int i, final int j) {
		// Two indices i and j.
		// Swaps the rows i and j of a quadratic matrix.
		// Warning: Changes the matrix.
		
		final int n = dimension;
		int[] row_i = new int[n];
		for (int k=0; k<n; k++) {
			row_i[k] = entries[i][k];
			entries[i][k] = entries[j][k];
			entries[j][k] = row_i[k];
		}
	}
	
	private static QuadraticMatrix gauss_elimination(final QuadraticMatrix M) {
		// Input: quadratic matrix M with last row 0,...,0,1.
		// Returns a quadratic integer matrix N in
		// row echelon form and as an upper triangle matrix
		// using Gaussian elimination.
		// Uses multiplication instead of division to stay in integers.
		final int n = M.dimension;
		
		// Copy of M that will be edited.
		QuadraticMatrix N = copy_matrix(M);
		
		// Gauss Elimination with multiplication instead of division.
		int h = 0;
		int k = 0;
		while (h<n && k<n) {
			int i_max = h;
			for (int i=h; i<n; i++) {
				if (Math.abs(N.entries[i][k]) > Math.abs(N.entries[i_max][k])) {
					i_max = i;
				}
			}
			if (N.entries[i_max][k] == 0) {
				k = k + 1;
			}
			else {
				N.swap_rows(h, i_max);
				for (int i=h+1; i<n; i++) {
					int f1 = 0;
					int f2 = 0;
					int gcd = 0;
					f1 = N.entries[i][k];
					f2 = N.entries[h][k];
					gcd = myRational.gcd(f1, f2);
					f1 = f1/gcd;
					f2 = f2/gcd;
					N.entries[i][k] = 0;
					for (int j=k+1; j<n; j++) {
						N.entries[i][j] = f2 * N.entries[i][j] - f1 * N.entries[h][j];
					}
				}
				h = h+1;
				k = k+1;
			}
		}
		
		// Bring in correct row echelon form.
		for (int l=1; l<n; l++) {
			int[][] entries_l = new int[n-l][n-l];
			for (int i=0; i<n-l; i++) {
				for (int j=0; j<n-l; j++) {
					entries_l[i][j] = N.entries[i+l][j+l];
				}
			}
			QuadraticMatrix N_l = new QuadraticMatrix(entries_l);
			QuadraticMatrix GN_l = gauss_elimination(N_l);
			for (int i=0; i<n-l; i++) {
				for (int j=0; j<n-l; j++) {
					N.entries[i+l][j+l] = GN_l.entries[i][j];
				}
			}
		}
		return N;
	}
	
	private static myRational[] backwards_substitution(final QuadraticMatrix M, final int s) {
		// Input: Quadratic integer matrix M.
		// Returns a solution of the LES as a Rational array.
		// When having choices, take s-th choice 1, other choices 0.
		// Warning: Only works if M is in row echelon form
		// and an upper triangle matrix
		// and has a row 0,...,0,1.
		// Computes a solution of the LES Ax = b
		// where M represents the LES Ax = b.
		
		QuadraticMatrix N = copy_matrix(M);
		final int n = N.dimension;
		if (N.entries[N.rank()-1][n-1] != 1) {
			throw new AssertionError("LES unsolvable.");
		}
		myRational[] p = new myRational[n-1];
		int expected = n-2;
		for (int i=0; i<n-1; i++) {
			p[i] = myRational.int_to_rational(0);
		}
		int s0 = 0;
		for (int i=N.rank()-2; i>=0; i--) {
			// Determine first column j with N.entries[i][j] != 0.
			int j=i;
			for (int l=i; l<n; l++) {
				if (N.entries[i][l] != 0) {
					j = l;
					break;
				}
			}
			while (j < expected) {
				s0 = s0 + 1;
				if (s0 == s) {
					p[expected] = myRational.int_to_rational(1);
				}
				expected = expected - 1;
			}
			expected = j - 1;
			p[j] = myRational.int_to_rational(N.entries[i][n-1]);
			for (int k=j+1; k<n-1; k++) {
				myRational tmp = new myRational(- N.entries[i][k] * p[k].numerator, p[k].denominator);
				p[j] = myRational.addition(p[j], tmp);
				p[j] = myRational.reduce_fraction(p[j]);
			}
			p[j].denominator = p[j].denominator * N.entries[i][j];
			p[j] = myRational.reduce_fraction(p[j]);
		}
		while (expected > -1) {
			s0 = s0 + 1;
			if (s0 == s) {
				p[expected] = myRational.int_to_rational(1);
			}
			expected = expected - 1;
		}
		return p;
	}
	
	private int rank() {
		// Returns the rank of a quadratic matrix.
		
		// Copy matrix.
		QuadraticMatrix M_copy = copy_matrix(this);
		QuadraticMatrix A = gauss_elimination(M_copy);
		// Compute the row echelon form using gaussian elimination.
		// Compute the number of non-zero diagonal entries.
		final int n = A.dimension;
		int zero_rows = 0;
		for (int i=0; i<n; i++) {
			for (int j=0; j<n; j++) {
				if (A.entries[i][j] != 0) { break; }
				if (j == n-1 && A.entries[i][j] == 0) {
					zero_rows = zero_rows + 1;
				}
			}
		}
		return n - zero_rows;
	}
	
	private int geometric_multiplicity(final int lambda) {
		// Input: an eigenvalue lambda.
		// Returns the geometric multiplicity of lambda with regard to a quadratic matrix M,
		// the dimension of ker(M-lambda*E) where E is the identity matrix.
		
		// The geometric multiplicity corresponds to the number of Jordan blocks for lambda.
		
		// Construct identity matrix.
		final int n = dimension;
		final QuadraticMatrix E = identity_matrix(n);
		
		// Construct matrix A = M - lambda * E.
		final QuadraticMatrix A = addition(this, scalar_multiplication(-lambda, E));

		// Use the dimension formula to get the dimension of ker(A).
		return n - A.rank();
	}
	
	private int number_of_blocks(final int lambda, final int s) {
		// Input: eigenvalue lambda and integer s.
		// Returns the number of Jordan blocks for lambda of size s
		// with regard to a quadratic matrix.
		
		final int n = dimension;
		final QuadraticMatrix E = identity_matrix(n);
		final QuadraticMatrix A = addition(this, scalar_multiplication(-lambda, E));		
		return (2 * (power(A,s)).geometric_multiplicity(0))
				- ((power(A, s+1)).geometric_multiplicity(0))
				- ((power(A, s-1)).geometric_multiplicity(0));
	}
	
	private static QuadraticMatrix create_jordan_block(final int lambda, final int s) {
		// Input: eigenvalue lambda, integer s.
		// Returns a Jordan block of size s with eigenvalue lambda.
		int[][] jordan_entries = new int[s][s];
		for (int i=0; i<s; i++) {
			jordan_entries[i][i] = lambda;
			if (i != s-1) {
				jordan_entries[i][i+1] = 1;
			}
		}
		final QuadraticMatrix J_lambda = new QuadraticMatrix(jordan_entries);
		return J_lambda;
	}
	
	private void add_jordan_block(final QuadraticMatrix B, final int start) {
		// Input: jordan block B, index start.
		// Adds jordan block B to quadratic jordan matrix J beginning at row start.
		
		if (dimension < B.dimension + start) {
			throw new AssertionError("Block does not fit into Jordan matrix");
		}
		final int s = B.dimension;
		for (int i=0; i<s; i++) {
			for (int j=0; j<s; j++) {
				entries[i+start][j+start] = B.entries[i][j];
			}
		}
	}
	
	public QuadraticMatrix jordan_matrix() {
		// Computes the jordan matrix of a quadratic matrix.
		
		final int n = dimension;
		int[][] jordan_entries = new int[n][n];
		QuadraticMatrix J = new QuadraticMatrix(jordan_entries);
		
		// Check if -1, 0, 1 are eigenvalues of M.
		final boolean[] eigenvalues = small_eigenvalues();
		
		// for each eigenvalue compute number of Jordan blocks.
		int current = 0;
		for (int e=-1; e<=1; e++) {
			if(eigenvalues[e+1]) {
				final int geom_mult = geometric_multiplicity(e);
				int[] number_of_blocks = new int[n + 1];
				int sum = 0;
				while (sum < geom_mult) {
					for (int s_e=1; s_e<=n; s_e++) {
						number_of_blocks[s_e] = number_of_blocks(e, s_e);
						sum = sum + number_of_blocks[s_e];
					}
				}
				for (int s=1; s<=n; s++) {
					for (int i=0; i<number_of_blocks[s]; i++) {
						QuadraticMatrix block = create_jordan_block(e,s);
						J.add_jordan_block(block, current);
						current = current + s;
					}
				}
			}
			
		}
		if (current != n) {
			throw new AssertionError("There is some eigenvalue with absolute value > 1");
		}
		return J;
	}
	
	private static QuadraticMatrix construct_les(final QuadraticMatrix M, final QuadraticMatrix J, final int j, final myRational[] p_jm1) {
		// Input: quadratic integer matrix M, its jordan matrix J,
		// the rational vector p_jm1, the column of the transformation
		// before the current column j.
		// Constructs the LES to compute the transformation matrix
		// of the Jordan normal form.
		
		final int n = M.dimension;
		int[][] les_entries = new int[n+1][n+1];
		QuadraticMatrix LES = new QuadraticMatrix(les_entries);
		les_entries[n][n] = 1;
		final QuadraticMatrix A = addition(M, scalar_multiplication(-J.entries[j][j], identity_matrix(n)));
		if (j == 0 || J.entries[j-1][j] == 0) {
			for (int l=0; l<n; l++) {
				for (int k=0; k<n; k++) {
					les_entries[l][k] = A.entries[l][k];
					les_entries[n][k] = 0;
				}
			}
			for (int i=0; i<n; i++) {
				les_entries[i][n] = 0;
			}
			les_entries[n][n] = 1;
		}
		else {
			for (int l=0; l<n; l++) {
				for (int k=0; k<n; k++) {
					les_entries[l][k] = p_jm1[l].denominator * A.entries[l][k];
					les_entries[n][k] = 0;
				}
			}
			for (int i=0; i<n; i++) {
				les_entries[i][n] = p_jm1[i].numerator;
			}
			les_entries[n][n] = 1;
		}
		return LES;
	}
	
	private static void add_vector_to_matrix(RationalMatrix M, final int j, final myRational[] p) {
		// Input: rational matrix M, index j and rational vector p.
		// Adds vector p to matrix M in column k.
		
		QuadraticMatrix P = M.int_matrix;
		final int n = P.dimension;
		for (int i=0; i<n; i++) {
			p[i] = myRational.reduce_fraction(p[i]);
			final int gcd = myRational.gcd(p[i].denominator, M.denominator);
			P.entries[i][j] = p[i].numerator * M.denominator/gcd;
			M.denominator = M.denominator * p[i].denominator/gcd;
			for (int l=0; l<n; l++) {
				for (int k=0; k<n; k++) {
					P.entries[l][k] = P.entries[l][k] * (p[i].denominator / gcd);
				}
			}
			P.entries[i][j] = P.entries[i][j] / (p[i].denominator / gcd);
		}
	}
	
	public static RationalMatrix modal_matrix(final QuadraticMatrix M, final QuadraticMatrix J) {
		// Input: a quadratic integer matrix M and its jordan matrix J.
		// Returns the transformation matrix P such that A = P*J*P^-1.
		
		final int n = M.dimension;
		// Check if M = J.
		boolean same = true;
		for (int i=0; i<n; i++) {
			for (int j=0; j<n; j++) {
				if (M.entries[i][j] != J.entries[i][j]) {
					same = false;
					break;
				}
			}
		}
		if (same) {
			RationalMatrix P = new RationalMatrix(1, identity_matrix(n));
			return P;
		}
		
		int[][] p_entries = new int[n][n];
		for (int i=0; i<n; i++) {
			for (int j=0; j<n; j++) {
				p_entries[i][j] = 0;
			}
		}
		QuadraticMatrix P_int = new QuadraticMatrix(p_entries);
		RationalMatrix P = new RationalMatrix(1, P_int);
		myRational[] p = new myRational[n];
		for (int i=0; i<n; i++) {
			p[i] = myRational.int_to_rational(0);
		}
		/*for (int j=0; j<n; j++) {
			QuadraticMatrix Q = construct_les(M, J, j, p);
			QuadraticMatrix QG = gauss_elimination(Q);
			p = backwards_substitution(QG);
			add_vector_to_matrix(P, j, p);
		}*/
		int s = 1;
		int in_block = 1;
		for (int j=0; j<n; j++) {
			QuadraticMatrix Q = construct_les(M, J, j, p);
			QuadraticMatrix QG = gauss_elimination(Q);
			if (j > 0) {
				if (J.entries[j][j] != J.entries[j-1][j-1]) {
					in_block = 1;
					s = 1;
				}
				else {
					if (J.entries[j-1][j] == 1) {
						s = 1;
					}
					else {
						in_block = in_block + 1;
						s = in_block;
					}
				}
			}
			p = backwards_substitution(QG, s);
			add_vector_to_matrix(P, j, p);
		}
		return P;
	}
}
