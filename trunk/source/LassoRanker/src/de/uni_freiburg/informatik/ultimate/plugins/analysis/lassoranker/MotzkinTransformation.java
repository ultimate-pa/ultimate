package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.util.*;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * This class applies the equivalence transformation given by
 * Motzkin's Transposition Theorem [1].
 * 
 * Motzkin's Theorem states that a system of linear inequalities is
 * unsatisfiable if and only if a contradiction can be derived from it by the
 * means of non-negative combinations of the equations:
 * 
 * <pre>
 * ∀x. ¬(A*x ≤ b /\ B*x < d)
 * 
 * if and only if
 * 
 * ∃λ, μ. λ ≥ 0 /\ μ ≥ 0 /\ λ*A + μ*B = 0 /\ λ*b + μ*d ≤ 0 /\
 *        (λ*b < 0 \/ μ ≠ 0)
 * </pre>
 * 
 * Here A and B are matrices, x, b and d are column vectors, and
 * λ and μ are row vectors.
 * 
 * Note that the quantifiers are not part of this class and are for
 * illustration purposes only.
 * 
 * [1] A. Schrijver. Theory of linear and integer programming.
 * Wiley-Interscience series in discrete mathematics and optimization. 1999.
 * 
 * @author Jan Leike
 */
public class MotzkinTransformation extends InstanceCounting {
	/**
	 * Prefix for the Motzkin coefficients λ and μ
	 */
	private static final String s_prefix = "motzkin_";
	
	/**
	 * The SMTLib script
	 */
	private Script m_script;
	
	/**
	 * List of affine terms corresponding to the system of inequalities
	 * Ax <= b /\ Bx < d
	 */
	public List<AffineInequality> terms = null;
	
	/**
	 * Vector x
	 */
	public Collection<TermVariable> transitionVariables = null;
	
	
	
	/**
	 * Whether this should be augmented with a supporting invariant
	 */
	public boolean wantsSI = false;
	
	/**
	 * Terms obtained after applying Farkas lemma (the transform() method).
	 * We store these terms only for debugging.
	 */
	private List<Term> transformedTerms = null;
	
	/**
	 * Construct the FarkasApplication object by just giving a script instance.
	 * 
	 * After filling all the public attributes, transform() can be called,
	 * returning the formula transformed according to Farkas' Lemma.
	 * 
	 * @param script The SMTLib script
	 */
	public MotzkinTransformation(Script script) {
		m_script = script;
	}
	
	/**
	 * Add a coefficient to the entailed map.
	 * Instead of overwriting a previous value, t will be added to the current
	 * value.
	 */
	public void addToEntailed(TermVariable var, Term t) {
		if (entailed == null) {
			entailed = new HashMap<TermVariable, Term>();
		}
		if (entailed.containsKey(var)) {
			entailed.put(var, m_script.term("+", entailed.get(var), t));
		} else {
			entailed.put(var, t);
		}
	}
	
	/**
	 * Build the inner product l * b.
	 * @param script SMTLib script
	 * @param vars list of variables corresponding to the vector l
	 * @param terms terms a list of affine terms whose constants terms form b
	 * @return an inequality built from the components above
	 */
	private Term mult1(List<Term> vars, List<AffineInequality> terms)
			throws SMTLIBException {
		Term t = m_script.decimal("0");
		for (int i = 0; i < terms.size(); ++i) {
			if (!terms.get(i).getConstant().equals(Rational.ZERO)) {
				Term c = AuxiliaryMethods.rationalToDecimal(m_script, 
						terms.get(i).getConstant());
				t = m_script.term("-", t, m_script.term("*", vars.get(i), c));
				// There needs to be a "-" here because the additive inverse
				// to b is saved in the list of affine terms. 
			}
		}
		return t;
	}
	
	/**
	 * Build an equality from the matrix multiplication lA = c.
	 * @param script SMTLib script
	 * @param vars list of variables corresponding to the vector l
	 * @param terms a list of affine terms corresponding to the matrix A
	 * @param progVar the column of A
	 * @param con the entry in c corresponding to the column in A
	 * @return an equation corresponding to the vector-matrix column
	 *          multiplication
	 */
	private Term mult2(List<Term> vars, List<AffineInequality> terms,
			TermVariable progVar, Term c) throws SMTLIBException {
		Term t = m_script.decimal("0");
		for (int i = 0; i < terms.size(); ++i) {
			Rational a = terms.get(i).getCoefficient(progVar);
			if (!a.equals(Rational.ZERO)) {
				Term cc = AuxiliaryMethods.rationalToDecimal(m_script, a);
				Term t_ = m_script.term("*", cc, vars.get(i));
				t = m_script.term("+", t, t_);
			}
		}
		if (c == null) {
			// Variable is not assigned
			c = m_script.decimal("0");
		}
		return m_script.term("=", t, c);
	}
	
	/**
	 * Returns the conjunction l >= 0 /\ l*A = c /\ l*b < gamma
	 * in form of a list.
	 * 
	 * All public attributes of this object have to been set before calling
	 * this: terms, transitionVariables, entailed, gamma, ieqsymb.
	 */
	public List<Term> transform() throws SMTLIBException {
		// Check if all attributes have been set
		assert(terms != null);
		assert(transitionVariables != null);
		assert(entailed != null);
		assert(gamma != null);
		assert(ieqsymb != null);
		
		// Determine the inequality symbol based on the state of ieqsymb
		String symb = null;
		if (ieqsymb == Inequality.LESS_THAN) {
			symb = "<";
		} else if (ieqsymb == Inequality.LESS_THAN_OR_EQUAL) {
			symb = "<=";
		} else {
			assert(false);
		}
		
		// Farkasing it up!
		List<Term> result = new ArrayList<Term>();
		List<Term> vars = new ArrayList<Term>();
		for (int i = 0; i < terms.size(); ++i) {
			Term var = AuxiliaryMethods.newRealConstant(m_script,
					s_prefix + m_instance + "_" + i);
			vars.add(var);
			Term term = m_script.term(">=", var, m_script.decimal("0"));
			if (Preferences.annotate_terms) {
				Annotation annot = new Annotation(":named", var+" non-negative");
				term = m_script.annotate(term, annot);
			}
			result.add(term);
		}
		{
			Term term = m_script.term(symb, mult1(vars, terms), gamma);
			if (Preferences.annotate_terms) {
				Annotation annot = new Annotation(":named", "instance" + 
						m_instance	+ " l*b<gamma term");
				term = m_script.annotate(term, annot);
			}
			result.add(term);
		}
		for (TermVariable var : transitionVariables) {
			Term c = entailed.get(var);
			if (c == null) {
				c = m_script.decimal("0");
			}
			Term term = mult2(vars, terms, var, c);
			if (Preferences.annotate_terms) {
				Annotation annot = new Annotation(":named", "instance" + 
						m_instance + " l*A=c, where c is coefficient of "+ var);
				term = m_script.annotate(term, annot);
			}
			result.add(term);
		}
		transformedTerms = result;
		return result;
	}
	
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("Terms before application of Farkas lemma\n");
		sb.append("  AffineTerms of antecedent: ");
		sb.append(terms);
		sb.append("\n");
		
		sb.append("  AffineTerms of succedent: ");
		if (entailed == null || gamma == null || ieqsymb == null) {
			sb.append("not yet added");
		} else {
			sb.append(prettyPrintEntailedInequality());
		}
		sb.append("\n");
		
		sb.append("Terms after application of Farkas lemma\n");
		if (transformedTerms == null) {
			sb.append("not yet computed\n");
		} else {
			for (Term term : transformedTerms) {
				sb.append("  " + term + "\n");
			}
		}
		return sb.toString();
	}
	
	private String prettyPrintEntailedInequality() {
		StringBuilder sb = new StringBuilder();
		Set<Entry<TermVariable, Term>> entries = entailed.entrySet();
		Iterator<Entry<TermVariable, Term>> it = entries.iterator();
		if (it.hasNext()) {
			Entry<TermVariable, Term> entry = it.next();
			sb.append(entry.getValue());
			sb.append(" * ");
			sb.append(entry.getKey());
			while (it.hasNext()) {
				entry = it.next();
				sb.append("  +  ");
				sb.append(entry.getValue());
				sb.append(" * ");
				sb.append(entry.getKey());
			}
		} else {
			sb.append("0");
		}
		switch (ieqsymb) {
		case LESS_THAN:
			sb.append("  <  ");
			break;
		case LESS_THAN_OR_EQUAL:
			sb.append("  <=  ");
			break;
		default:
			throw new AssertionError();
		}
		sb.append(gamma);
		return sb.toString();
	}
}
