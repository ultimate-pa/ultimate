package caseStudies;

import pea.CDD;
import pea.BooleanDecision;

public class TestSR1 {

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		CDD c1=BooleanDecision.create("A = 1 \u2228 B = 1");
		CDD c2=BooleanDecision.create("A = 1");
		CDD c3=BooleanDecision.create("B = 1");
		CDD c4=c2.or(c3);
		
		System.out.println( c2.implies(c1) );
		System.out.println( c2.implies(c4) );

	}

}
