package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

public class SubstitutionApplier extends NonRecursive {
	
	private final class AnnotationBuilder implements Walker {
		
		private AnnotatedTerm m_Term;
		
		public AnnotationBuilder(AnnotatedTerm term) {
			m_Term = term;
		}

		@Override
		public void walk(NonRecursive engine) {
			Term converted = m_Converted.pop();
			Term res = converted.getTheory().annotatedTerm(
					m_Term.getAnnotations(), converted);
			m_Converted.push(res);
		}
		
	}
	
	private final class ApplicationTermBuilder implements Walker {
		
		private ApplicationTerm m_Term;
		
		public ApplicationTermBuilder(ApplicationTerm term) {
			m_Term = term;
		}

		@Override
		public void walk(NonRecursive engine) {
			Term[] newArgs = new Term[m_Term.getParameters().length];
			for (int i = 0; i < newArgs.length; ++i)
				newArgs[i] = m_Converted.pop();
			Term res = m_Term.getTheory().term(m_Term.getFunction(), newArgs);
			m_Converted.push(res);
		}
		
	}
	
	private final class LetBuilder implements Walker {
		
		private LetTerm m_Term;
		
		public LetBuilder(LetTerm term) {
			m_Term = term;
		}

		@Override
		public void walk(NonRecursive engine) {
			Term subform = m_Converted.pop();
			Term[] newVals = new Term[m_Term.getValues().length];
			for (int i = 0; i < newVals.length; ++i)
				newVals[i] = m_Converted.pop();
			Term res = m_Term.getTheory().let(
					m_Term.getVariables(), newVals, subform);
			m_Converted.push(res);
		}
		
	}
	
	private final class QuantifierBuilder implements Walker {

		private QuantifiedFormula m_Term;
		
		public QuantifierBuilder(QuantifiedFormula term) {
			m_Term = term;
		}
		
		@Override
		public void walk(NonRecursive engine) {
			Term subform = m_Converted.pop();
			Theory t = m_Term.getTheory();
			Term res = m_Term.getQuantifier() == QuantifiedFormula.EXISTS ?
					t.exists(m_Term.getVariables(), subform) :
						t.forall(m_Term.getVariables(), subform);
			m_Converted.push(res);
		}
		
	}
	
	private final class DepthDescender extends TermWalker {

		private int m_Depth;
		
		public DepthDescender(Term term, int depth) {
			super(term);
			m_Depth = depth;
		}

		@Override
		public void walk(NonRecursive walker) {
			if (m_Depth == SubstitutionApplier.this.m_Depth) {
				// Apply substitution
				boolean expectedTrue = m_It.hasNext();
				assert expectedTrue;
				if (m_Subst != null && m_Subst.matches(getTerm())) {
					System.err.println("Substitution " + m_Subst + " matches " + getTerm());
					if (m_Subst.isActive()) {
						m_Converted.push(m_Subst.apply(getTerm()));
						Cmd add = m_Subst.getAdditionalCmd(getTerm());
						if (add != null)
							m_Adds.add(add);
					} else
						m_Converted.push(getTerm());
					// We can step here since we found a (possibly deactivated)
					// match.  If the term does not match, we should not step!
					stepSubst();
				} else {
					System.err.println("Substitution " + m_Subst + " does not match " + getTerm());
					// We don't need to descend since we will never change
					// anything at lower depths.
					m_Converted.push(getTerm());
				}
			} else
				super.walk(walker);
		}

		@Override
		public void walk(NonRecursive walker, ConstantTerm term) {
			m_Converted.push(term);
		}

		@Override
		public void walk(NonRecursive walker, AnnotatedTerm term) {
			walker.enqueueWalker(new AnnotationBuilder(term));
			walker.enqueueWalker(
					new DepthDescender(term.getSubterm(), m_Depth + 1));
		}

		@Override
		public void walk(NonRecursive walker, ApplicationTerm term) {
			walker.enqueueWalker(new ApplicationTermBuilder(term));
			for (Term p : term.getParameters())
				walker.enqueueWalker(new DepthDescender(p, m_Depth + 1));
		}

		@Override
		public void walk(NonRecursive walker, LetTerm term) {
			walker.enqueueWalker(new LetBuilder(term));
			for (Term v : term.getValues())
				walker.enqueueWalker(new DepthDescender(v, m_Depth + 1));
			walker.enqueueWalker(
					new DepthDescender(term.getSubTerm(), m_Depth + 1));
		}

		@Override
		public void walk(NonRecursive walker, QuantifiedFormula term) {
			walker.enqueueWalker(new QuantifierBuilder(term));
			walker.enqueueWalker(
					new DepthDescender(term.getSubformula(), m_Depth + 1));
		}

		@Override
		public void walk(NonRecursive walker, TermVariable term) {
			m_Converted.push(term);
		}
		
	}
	
	private int m_Depth;
	private List<Substitution> m_Substs;
	private Iterator<Substitution> m_It;
	private Substitution m_Subst;
	
	private ArrayDeque<Term> m_Converted = new ArrayDeque<Term>();
	private List<Cmd> m_Adds = new ArrayList<Cmd>();

	void stepSubst() {
		while (m_It.hasNext()) {
			m_Subst = m_It.next();
			if (!m_Subst.isSuccess())
				return;
		}
		m_Subst = null;
	}
	
	public void init(int depth, List<Substitution> substs) {
		m_Depth = depth;
		m_Substs = substs;
		m_It = m_Substs.iterator();
		stepSubst();
	}
	
	public Term apply(Term term) {
		run(new DepthDescender(term, 0));
		return m_Converted.pop();
	}
	
	public List<Cmd> getAdds() {
		List<Cmd> res = m_Adds;
		m_Adds = new ArrayList<Cmd>();
		return res;
	}
	
}
