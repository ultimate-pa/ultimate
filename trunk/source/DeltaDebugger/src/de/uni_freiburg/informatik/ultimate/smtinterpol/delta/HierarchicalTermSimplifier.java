package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

public class HierarchicalTermSimplifier extends TermTransformer {
	
	private final static String FRESH_PREFIX = ".DELTA_SIMPLIFY_";
	private static int m_FreshCounter = 0;
	
	static String getFreshName() {
		return FRESH_PREFIX + ++m_FreshCounter;
	}
	
	static String getLastFreshName() {
		return FRESH_PREFIX + m_FreshCounter;
	}
	
	private static interface Action {
		/**
		 * Apply the action to an input term.
		 * @param original The input term.
		 * @return Result of applying the action to the input term or
		 *         <code>null</code> if the action was not applicable.
		 */
		Term apply(Term original);
		/**
		 * Return the next action to apply to this term.
		 * @param original The input term.
		 * @return Next action or <code>null</code> if no further action exists.
		 */
		Action next(Term original);
		/**
		 * Return a list of commands that need to be added before this command.
		 * @param original TODO
		 * @return Non-<code>null</code> list of commands.
		 */
		Cmd additionalCmds(Term original);
	}
	
	public static class AnnotationSimp implements Action {
		
		public static Action INSTANCE = new AnnotationSimp();

		private boolean hasNames(AnnotatedTerm at) {
			for (Annotation a : at.getAnnotations())
				if (a.getKey().equals(":named"))
					return true;
			return false;
		}
		
		@Override
		public Term apply(Term original) {
			if (original instanceof AnnotatedTerm) {
				AnnotatedTerm at = (AnnotatedTerm) original;
				if (hasNames(at))
					return null;
				return at.getSubterm();
			}
			return null;
		}

		@Override
		public Action next(Term original) {
			if (original instanceof AnnotatedTerm &&
					hasNames(((AnnotatedTerm) original)))
				return null;
			return ReplaceTrue.INSTANCE;
		}

		@Override
		public Cmd additionalCmds(Term original) {
			return null;
		}		
	}
	
	public static class ReplaceTrue implements Action {

		public static Action INSTANCE = new ReplaceTrue();
		
		@Override
		public Term apply(Term original) {
			return original.getSort() == original.getTheory().getBooleanSort() ?
				original.getTheory().TRUE : null;
		}

		@Override
		public Action next(Term original) {
			return original.getSort() == original.getTheory().getBooleanSort() ?
					ReplaceFalse.INSTANCE : ReplaceZero.INSTANCE;
		}

		@Override
		public Cmd additionalCmds(Term original) {
			return null;
		}		
		
	}
	
	public static class ReplaceFalse implements Action {

		public static final Action INSTANCE = new ReplaceFalse();

		@Override
		public Term apply(Term original) {
			return original.getTheory().FALSE;
		}

		@Override
		public Action next(Term original) {
			return FApp.INSTANCE;
		}

		@Override
		public Cmd additionalCmds(Term original) {
			return null;
		}		
		
	}
	
	public static class ReplaceZero implements Action {
		
		public static Action INSTANCE = new ReplaceZero();

		@Override
		public Term apply(Term original) {
			Sort s = original.getSort();
			if (s.isNumericSort()) {
				if (s.getName().equals("Real"))
					return original.getTheory().rational(
							BigInteger.ZERO, BigInteger.ONE);
				else
					return original.getTheory().numeral(BigInteger.ZERO);
			}
			return null;
		}

		@Override
		public Action next(Term original) {
			return Store.INSTANCE;
		}

		@Override
		public Cmd additionalCmds(Term original) {
			return null;
		}		
		
	}
	
	public static class Store implements Action {
		
		public final static Action INSTANCE = new Store();

		private boolean isStore(ApplicationTerm at) {
			return at.getFunction().getName().equals("store");
		}
		
		@Override
		public Term apply(Term original) {
			if (original instanceof ApplicationTerm) {
				ApplicationTerm at = (ApplicationTerm) original;
				if (isStore(at))
					return at.getParameters()[0];
			}
			return null;
		}

		@Override
		public Action next(Term original) {
			return null;
		}

		@Override
		public Cmd additionalCmds(Term original) {
			return null;
		}		
		
	}
	
	public static class IteRight implements Action {

		public static final Action INSTANCE = new IteRight();
		
		private boolean isIte(ApplicationTerm at) {
			return at.getFunction().getName().equals("ite");
		}
		
		@Override
		public Term apply(Term original) {
			if (original instanceof ApplicationTerm) {
				ApplicationTerm at = (ApplicationTerm) original;
				if (isIte(at))
					return at.getParameters()[2];
			}
			return null;
		}

		@Override
		public Action next(Term original) {
			return null;
		}

		@Override
		public Cmd additionalCmds(Term original) {
			return null;
		}
		
	}
	
	public static class IteLeft implements Action {
		
		public static final Action INSTANCE = new IteLeft();

		private boolean isIte(ApplicationTerm at) {
			return at.getFunction().getName().equals("ite");
		}
		
		@Override
		public Term apply(Term original) {
			if (original instanceof ApplicationTerm) {
				ApplicationTerm at = (ApplicationTerm) original;
				if (isIte(at))
					return at.getParameters()[1];
			}
			return null;
		}

		@Override
		public Action next(Term original) {
			return IteRight.INSTANCE;
		}

		@Override
		public Cmd additionalCmds(Term original) {
			return null;
		}
		
	}
	
	public static class FApp implements Action {
		
		public static final Action INSTANCE = new FApp();

		private final static Sort[]	EMPTY_SORT_ARRAY = {};
		
		@Override
		public Term apply(Term original) {
			if (original instanceof ApplicationTerm && 
					((ApplicationTerm) original).getParameters().length > 0) {
				String fresh = getFreshName();
				Theory t = original.getTheory();
				return t.term(
						t.declareFunction(
								fresh, EMPTY_SORT_ARRAY, original.getSort()));
			}
			return null;
		}

		@Override
		public Action next(Term original) {
			return IteLeft.INSTANCE;
		}

		@Override
		public Cmd additionalCmds(Term original) {
			if (original instanceof ApplicationTerm && 
					((ApplicationTerm) original).getParameters().length > 0) {
				return new DeclareFun(
						getLastFreshName(),
						EMPTY_SORT_ARRAY,
						original.getSort());
			}
			return null;
		}
		
	}
	
	private Map<Term, Action> m_Actions = new HashMap<Term, Action>();
	private List<Cmd> m_AdditionalCmds = new ArrayList<Cmd>();
	
	public void init(Term input) {
		m_Actions.put(input, AnnotationSimp.INSTANCE);
	}
	
	public List<Cmd> getAdditionalCommands() {
		return m_AdditionalCmds;
	}
	
	public Term step(Term input) {
		m_AdditionalCmds.clear();
		return transform(input);
	}

	@Override
	protected void convert(Term term) {
		Action action = m_Actions.get(term);
		if (action == null)
			super.convert(term);
		while (action != null) {
			Term res = action.apply(term);
			if (res != null) {
				// Store successful action
				m_Actions.put(term, action);
				Cmd add = action.additionalCmds(term);
				if (add != null)
					m_AdditionalCmds.add(add);
				setResult(res);
				return;
			}
			action = action.next(term);
		}
		// No applicable action found => descend
		if (term instanceof AnnotatedTerm)
			init(((AnnotatedTerm) term).getSubterm());
		else if (term instanceof ApplicationTerm) {
			ApplicationTerm at = (ApplicationTerm) term;
			for (Term t : at.getParameters())
				init(t);
		} else if (term instanceof LetTerm) {
			LetTerm lt = (LetTerm) term;
			for (Term t : lt.getValues())
				init(t);
			init(lt.getSubTerm());
		} else if (term instanceof QuantifiedFormula)
			init(((QuantifiedFormula) term).getSubformula());
	}

}
