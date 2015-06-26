package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;

import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.annotation.AbstractAnnotations;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.util.relation.Pair;

public class AnnotatingRcfgAbstractStateStorageProvider extends BaseRcfgAbstractStateStorageProvider {

	public AnnotatingRcfgAbstractStateStorageProvider(IAbstractStateBinaryOperator<CodeBlock, BoogieVar> mergeOperator) {
		super(mergeOperator);
	}

	protected Deque<Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>>> getStates(RCFGNode node) {
		assert node != null;
		AbsIntAnnotation rtr = AbsIntAnnotation.getAnnotation(node);
		if (rtr == null) {
			rtr = new AbsIntAnnotation();
			rtr.annotate(node);
		}
		return rtr.mStates;
	}

	private static final class AbsIntAnnotation extends AbstractAnnotations {

		private static final String KEY = AbsIntAnnotation.class.getSimpleName();
		private static final String[] FIELD_NAMES = new String[] { "States" };
		private static final long serialVersionUID = 1L;
		private final Deque<Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>>> mStates;

		private AbsIntAnnotation() {
			mStates = new ArrayDeque<>();
		}

		@Override
		protected String[] getFieldNames() {
			return FIELD_NAMES;
		}

		@Override
		protected Object getFieldValue(String field) {
			if (FIELD_NAMES[0].equals(field)) {
				// states
				final ArrayList<String> rtr = new ArrayList<>();
				for (final Pair<CodeBlock, IAbstractState<CodeBlock, BoogieVar>> entry : mStates) {
					rtr.add(new StringBuilder().append("[").append(entry.getSecond().hashCode()).append("] ")
							.append(entry.getSecond().toLogString()).append(" (from ")
							.append(entry.getFirst().getPrettyPrintedStatements()).append(")").toString());
				}
				return rtr.toArray(new String[rtr.size()]);
			}
			return null;
		}

		public void annotate(IElement elem) {
			elem.getPayload().getAnnotations().put(KEY, this);
		}

		public static AbsIntAnnotation getAnnotation(IElement elem) {
			if (!elem.hasPayload()) {
				return null;
			}
			if (!elem.getPayload().hasAnnotation()) {
				return null;
			}
			return (AbsIntAnnotation) elem.getPayload().getAnnotations().get(KEY);
		}
	}
}
