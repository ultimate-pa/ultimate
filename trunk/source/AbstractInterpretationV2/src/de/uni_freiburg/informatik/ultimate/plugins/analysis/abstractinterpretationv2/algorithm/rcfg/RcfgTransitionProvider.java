package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ITransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

public class RcfgTransitionProvider implements ITransitionProvider<CodeBlock> {

	@Override
	public Collection<CodeBlock> filterInitialElements(Collection<CodeBlock> elems) {
		if (elems == null) {
			return Collections.emptyList();
		}
		final List<CodeBlock> rtr = new ArrayList<>(elems.size());
		for (final CodeBlock elem : elems) {
			if (!(elem instanceof Summary)) {
				rtr.add(elem);
			}
		}
		return rtr;
	}
	
	@Override
	public Collection<CodeBlock> getSuccessors(CodeBlock elem) {
		final RCFGNode target = elem.getTarget();
		if (target == null) {
			return Collections.emptyList();
		}
		final List<RCFGEdge> successors = target.getOutgoingEdges();
		final Collection<CodeBlock> rtr = convertToCodeBlock(successors);
		return rtr;
	}

	@Override
	public boolean isPostErrorLocation(CodeBlock elem) {
		final RCFGNode target = elem.getTarget();
		if (target instanceof ProgramPoint) {
			ProgramPoint progPoint = (ProgramPoint) target;
			return progPoint.isErrorLocation();
		}
		return false;
	}

	@Override
	public String toLogString(CodeBlock elem) {
		return elem.toString();
	}

	@Override
	public Collection<CodeBlock> getSiblings(CodeBlock elem) {
		final RCFGNode target = elem.getTarget();
		if (target == null) {
			return Collections.emptyList();
		}
		final Collection<CodeBlock> siblings = convertToCodeBlock(target.getIncomingEdges());
		final List<CodeBlock> rtr = new ArrayList<CodeBlock>(siblings.size() - 1);
		for (final CodeBlock sibling : siblings) {
			if (sibling.equals(elem)) {
				continue;
			}
			rtr.add(sibling);
		}
		return rtr;
	}

	private Collection<CodeBlock> convertToCodeBlock(final Collection<RCFGEdge> successors) {
		if (successors == null) {
			return Collections.emptyList();
		}
		final List<CodeBlock> rtr = new ArrayList<>(successors.size());
		for (final RCFGEdge successor : successors) {
			if (successor instanceof CodeBlock && !(successor instanceof Summary)) {
				rtr.add((CodeBlock) successor);
			}
		}
		return rtr;
	}
}
