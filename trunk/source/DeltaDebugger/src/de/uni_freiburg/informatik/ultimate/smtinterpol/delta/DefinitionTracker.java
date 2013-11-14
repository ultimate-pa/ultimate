package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class DefinitionTracker extends NonRecursive {
	private class Walker extends TermWalker {

		public Walker(Term term) {
			super(term);
		}

		@Override
		public void walk(NonRecursive walker, ConstantTerm term) {}

		@Override
		public void walk(NonRecursive walker, AnnotatedTerm term) {
			walker.enqueueWalker(new Walker(term.getSubterm()));
		}

		@Override
		public void walk(NonRecursive walker, ApplicationTerm term) {
			FunctionSymbol fs = term.getFunction();
			if (!fs.isIntern())
				track(fs.getName());
			for (Term p : term.getParameters())
				walker.enqueueWalker(new Walker(p));
		}

		@Override
		public void walk(NonRecursive walker, LetTerm term) {
			for (Term bound : term.getValues())
				walker.enqueueWalker(new Walker(bound));
			walker.enqueueWalker(new Walker(term.getSubTerm()));
		}

		@Override
		public void walk(NonRecursive walker, QuantifiedFormula term) {
			walker.enqueueWalker(new Walker(term.getSubformula()));
		}

		@Override
		public void walk(NonRecursive walker, TermVariable term) {}
		
	}
	
	private Map<String, Cmd> m_Ctx;
	private Set<Cmd> m_Used;
	
	public DefinitionTracker(Map<String, Cmd> ctx, Set<Cmd> used) {
		m_Ctx = ctx;
		m_Used = used;
	}
	
	public void track(Term t) {
		run(new Walker(t));
	}
	
	private void track(String fun) {
		Cmd definition = m_Ctx.get(fun);
		if (definition == null)
			throw new InternalError("No definition found for " + fun);
		m_Used.add(definition);
	}
}
