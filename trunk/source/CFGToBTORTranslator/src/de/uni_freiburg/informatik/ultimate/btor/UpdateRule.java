package de.uni_freiburg.informatik.ultimate.btor;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.btor.expression.BtorExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.StateExpression;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class UpdateRule {
	private final DebugIdentifier targetIdentifier;
	private final Term condition;
	private final TransFormula tf;
	IcfgEdge icfgEdge;
	public BtorScript script;

	public UpdateRule(final Term condition, final DebugIdentifier targetIdentifier, final TransFormula tf,
			final IcfgEdge icfgEdge, final BtorScript script) {
		this.condition = condition;
		this.targetIdentifier = targetIdentifier;
		this.tf = tf;
		this.icfgEdge = icfgEdge;
		this.script = script;
	}

	public DebugIdentifier getTargetIdentifier() {
		return targetIdentifier;
	}

	public Term getCondition() {
		return condition;
	}

	public TransFormula getTransFormula() {
		return tf;
	}

	public IcfgEdge getIcfgEdge() {
		return icfgEdge;
	}

	public BtorExpression getConditionAsExpression(final Map<String, StateExpression> variableMap) {
		return TermToBtorUtil.convertConditionalToBtorExpression(condition, tf, variableMap, null, script);
	}
}
