package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive.TermWalker;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class NamedHelper {
	
	private final class NamedCollector extends TermWalker {
		public NamedCollector(Term term) {
			super(term);
		}

		@Override
		public void walk(NonRecursive walker, ConstantTerm term) {}

		@Override
		public void walk(NonRecursive walker, AnnotatedTerm term) {
			for (Annotation annot : term.getAnnotations())
				if (annot.getKey().equals(":named"))
					m_Names.put(annot.getValue().toString(), m_Cmd);
		}

		@Override
		public void walk(NonRecursive walker, ApplicationTerm term) {
			for (Term t : term.getParameters())
				walker.enqueueWalker(new NamedDetector(t));
		}

		@Override
		public void walk(NonRecursive walker, LetTerm term) {
			for (Term t : term.getValues())
				walker.enqueueWalker(new NamedDetector(t));
			walker.enqueueWalker(new NamedDetector(term.getSubTerm()));
		}

		@Override
		public void walk(NonRecursive walker, QuantifiedFormula term) {
			walker.enqueueWalker(new NamedDetector(term.getSubformula()));
		}

		@Override
		public void walk(NonRecursive walker, TermVariable term) {}
	}
	
	private final class NamedDetector extends TermWalker {

		public NamedDetector(Term term) {
			super(term);
		}

		@Override
		public void walk(NonRecursive walker, ConstantTerm term) {}

		@Override
		public void walk(NonRecursive walker, AnnotatedTerm term) {
			for (Annotation annot : term.getAnnotations())
				if (annot.getKey().equals(":named"))
					m_HasNames = true;
		}

		@Override
		public void walk(NonRecursive walker, ApplicationTerm term) {
			for (Term t : term.getParameters())
				walker.enqueueWalker(new NamedDetector(t));
		}

		@Override
		public void walk(NonRecursive walker, LetTerm term) {
			for (Term t : term.getValues())
				walker.enqueueWalker(new NamedDetector(t));
			walker.enqueueWalker(new NamedDetector(term.getSubTerm()));
		}

		@Override
		public void walk(NonRecursive walker, QuantifiedFormula term) {
			walker.enqueueWalker(new NamedDetector(term.getSubformula()));
		}

		@Override
		public void walk(NonRecursive walker, TermVariable term) {}
		
	}
	
	private boolean m_HasNames;
	private Map<String, Cmd> m_Names;
	private Cmd m_Cmd;
	
	public boolean checkTerm(Term t) {
		m_HasNames = false;
		new NonRecursive().run(new NamedDetector(t));
		return m_HasNames;
	}
	
	public void addNames(Term t, Map<String, Cmd> context, Cmd cmd) {
		m_Names = context;
		m_Cmd = cmd;
		new NonRecursive().run(new NamedCollector(t));
	}
}
