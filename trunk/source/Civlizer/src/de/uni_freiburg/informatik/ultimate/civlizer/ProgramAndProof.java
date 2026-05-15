package de.uni_freiburg.informatik.ultimate.civlizer;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.OwickiGriesAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.WitnessInvariant;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

class ProgramAndProof {

	private Unit mBoogieAst = null;
	private BoogieIcfgContainer mIcfg = null;
	private List<OwickiGriesAnnotation> mProof = null;

	private ThreadTemplateVisitor mTemplateVisitor = null;
	private Map<String, List<Tid>> mMapToTid;
	private Set<Tid> mTids;

	ProgramAndProof() {}

	ThreadTemplateVisitor getTemplateVisitor() {
		return mTemplateVisitor;
	}

	BoogieIcfgContainer getIcfg() {
		return mIcfg;
	}

	Unit getBoogieAst() {
		return mBoogieAst;
	}

	List<OwickiGriesAnnotation> getProof() {
		return mProof;
	}

	void setBoogieAst(Unit boogieAst) {
		mBoogieAst = boogieAst;
		mTemplateVisitor = new ThreadTemplateVisitor(boogieAst);
	}

	void setIcfg(BoogieIcfgContainer icfg) {
		mIcfg = icfg;
	}

	void setProof(List<OwickiGriesAnnotation> proof) {
		mProof = proof;
	}

	boolean isFull() {
		return mBoogieAst != null && mIcfg != null && mProof != null;
	}

	void preprocess() {
		mTemplateVisitor = new ThreadTemplateVisitor(mBoogieAst);
	}

	//Map<Integer, Expression>
	Map<ILocation, Expression> getAnnotation(String procName) {
		Map<ILocation, Expression> result = new HashMap<>();
		for (BoogieIcfgLocation loc : mIcfg.getProgramPoints().get(procName).values()) {
			final var invariant = (WitnessInvariant.getAnnotation(loc) != null) ? (Expression) WitnessInvariant.getAnnotation(loc).getInvariant() : null;
			final var codeLocation = (ILocation) ILocation.getAnnotation(loc);
			System.out.println(invariant);
			System.out.println(codeLocation);
			result.put(codeLocation, invariant);
		}

		return result;
	}
}