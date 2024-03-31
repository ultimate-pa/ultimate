package de.uni_freiburg.informatik.ultimate.btorutils;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class AssignmentRule {
	public DebugIdentifier assignmentLocationIdentifier;
	public IProgramVar lhs;
	public Term rhs;

	public AssignmentRule(final DebugIdentifier assignmentLocationIdentifier, final IProgramVar lhs, final Term rhs) {
		this.assignmentLocationIdentifier = assignmentLocationIdentifier;
		this.lhs = lhs;
		this.rhs = rhs;
	}

	public static List<AssignmentRule> getAssignmentsFromTransition(final DebugIdentifier assignmentLocationIdentifier,
			final TransFormula tf) {
		return new ArrayList<>();
	}
}
