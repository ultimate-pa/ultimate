package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.jordan;

public class myRational {
	
	// Class for rational numbers as fractions.
	// Rational number represented by its integer numerator and denominator.
	
	int numerator;
	int denominator;
	
	public myRational(int num, int denom) {
		// Constructor.
		
		numerator = num;
		denominator = denom;
		assert denom != 0 : "division by 0";
	}
	
	public static int gcd(int a, int b) {
		// Input: two integers a and b.
		// Returns the greatest common divisor of a and b.
		// Used to reduce fractions and keep numbers small.
		
		int t = 0;
		while (b != 0) {
			t = b;
			b = a % b;
			a = t;
		}
		return a;
	}
	
	public static myRational reduce_fraction(myRational r) {
		// Input: rational number r.
		// Changes numerator and denominator such that r is represented as
		// completely reduced fraction.
		final int gcd = gcd(r.numerator, r.denominator);
		if (gcd == 0) {
			return int_to_rational(0);
		}
		r.numerator = r.numerator / gcd;
		r.denominator = r.denominator / gcd;
		return r;
	}
	
	public static myRational addition(final myRational a, final myRational b) {
		// Input: two rational numbers a and b.
		// Returns the a + b.
		final int sum_num = a.numerator * b.denominator + b.numerator * a.denominator;
		final int sum_denom = a.denominator * b.denominator;
		myRational sum = new myRational(sum_num, sum_denom);
		reduce_fraction(sum);
		return sum;
	}
	
	public static myRational int_to_rational(final int a) {
		// Input: an integer a.
		// Returns the integer a represented as rational number a/1.
		
		final myRational c = new myRational(a,1);
		return c;
	}
}
