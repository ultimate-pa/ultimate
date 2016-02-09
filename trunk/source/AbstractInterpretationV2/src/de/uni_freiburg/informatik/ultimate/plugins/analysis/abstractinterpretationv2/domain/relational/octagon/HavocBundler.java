package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgStatementExtractor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class HavocBundler {

	private final RcfgStatementExtractor mStatementExtractor;
	private final Map<CodeBlock, List<Statement>> mCache;
	
	public HavocBundler() {
		mStatementExtractor = new RcfgStatementExtractor();
		mCache = new HashMap<>();
	}
	
	public List<Statement> bundleHavocsCached(CodeBlock block) {
		// CodeBlock is used as parameter, because CodeBlock does not overwrite equals => faster map access
		List<Statement> cachedResult = mCache.get(block);
		if (cachedResult == null) {
			cachedResult = bundleHavocs(mStatementExtractor.process(block));
			mCache.put(block, cachedResult);
		}
		return cachedResult;
	}

	private List<Statement> bundleHavocs(List<Statement> block) {
		List<Statement> result = new ArrayList<>(block.size());
		List<HavocStatement> successiveHavocs = new ArrayList<>(block.size());
		for (Statement statement : block) {
			if (statement instanceof HavocStatement) {
				successiveHavocs.add((HavocStatement) statement);
			} else {
				if (!successiveHavocs.isEmpty()) {
					result.add(joinHavocs(successiveHavocs));
					successiveHavocs.clear();
				}
				result.add(statement);
			}
		}
		if (!successiveHavocs.isEmpty()) {
			result.add(joinHavocs(successiveHavocs));
		}
		return result;
	}
	
	private HavocStatement joinHavocs(List<HavocStatement> successiveHavocs) {
		if (successiveHavocs.size() == 1) {
			return successiveHavocs.get(0);
		}
		List<VariableLHS> vars = new ArrayList<>();
		for (HavocStatement hs : successiveHavocs) {
			for (VariableLHS var : hs.getIdentifiers()) {
				vars.add(var);
			}
		}
		VariableLHS[] joinedVariables = vars.toArray(new VariableLHS[vars.size()]);
		ILocation location = successiveHavocs.isEmpty() ? null : successiveHavocs.get(0).getLocation();
		return new HavocStatement(location, joinedVariables);
	}
}
