package de.uni_freiburg.informatik.ultimate.civlizer;

import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.OwickiGriesAnnotation;

class ProgramAndProof {

	private Unit mBoogieAst = null;
	private List<OwickiGriesAnnotation> mProof = null;

	private Map<String, List<Tid>> mMapToTid;
	private Set<Tid> mTids;

	ProgramAndProof() {}

	Map<String, List<Tid>> getMapToTid() {
		return mMapToTid;
	}

	Set<Tid> getTids() {
		return mTids;
	}

	Unit getBoogieAst() {
		return mBoogieAst;
	}

	List<OwickiGriesAnnotation> getProof() {
		return mProof;
	}

	void setBoogieAst(Unit boogieAst) {
		mBoogieAst = boogieAst;
	}

	void setProof(List<OwickiGriesAnnotation> proof) {
		mProof = proof;
	}

	boolean isFull() {
		return mBoogieAst != null && mProof != null;
	}

	void preprocess() {
		mMapToTid = ThreadTemplateVisitor.getMapToTid(mBoogieAst);
		mTids = ThreadTemplateVisitor.getValuesFromMap(mMapToTid);
	}
}