package de.uni_freiburg.informatik.ultimate.civlizer;

import java.util.List;
import java.util.Map;
import java.util.HashMap;
import java.util.Set;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.boogie.ast.*;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.WitnessInvariant;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.OwickiGriesAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.WitnessGhostUpdate;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;

class ProgramAndProof {

	private Unit mBoogieAst = null;
	private BoogieIcfgContainer mIcfg = null;
	private List<OwickiGriesAnnotation> mProof = null;
	private Map<ILocation, Set<CallStatement>> mGhostUpdateMap = null;
	private ThreadTemplateVisitor mTemplateVisitor = null;

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

	Map<ILocation, Set<CallStatement>> getGhostUpdateMap() {
		return mGhostUpdateMap;
	}

	void preprocess() {
		mTemplateVisitor = new ThreadTemplateVisitor(mBoogieAst);
		mGhostUpdateMap = new HashMap<>();

		final var programPoints = mIcfg.getProgramPoints();

		for (final Map<?, BoogieIcfgLocation> innerMap : programPoints.values()) {
			for (final BoogieIcfgLocation location : innerMap.values()) {

				for (final var edge : location.getOutgoingEdges()) {
					if (WitnessGhostUpdate.getAnnotation(edge) != null) {
						
						Set<CallStatement> assignments = new HashSet<>();
						ILocation loc = location.getBoogieASTNode().getLocation();

						final Map<?, ?> update =
								WitnessGhostUpdate.getAnnotation(edge).getUpdate();

						// TODO improve readability

						for (final Map.Entry<?, ?> updateEntry : update.entrySet()) {
							
							IdentifierExpression layerNum = new IdentifierExpression(
								loc, 
								BoogieType.createPlaceholderType(0),
								"2",
								new DeclarationInformation(DeclarationInformation.StorageClass.GLOBAL, null)
							);

							CallStatement assign = new CallStatement(
								loc,
								new NamedAttribute[] {
									new NamedAttribute(
										loc, 
										"layer", 
										new Expression[] {
											layerNum, layerNum
										}
									)
								},
								false,
								new VariableLHS[] {
									new VariableLHS(loc, updateEntry.getKey().toString())
								}, 
								"Copy",
								new Expression[] {
									(Expression)updateEntry.getValue()
								});
							assignments.add(assign);
						}
						mGhostUpdateMap.put(
							loc, 
							assignments
						);
					}
				}
			}
		}
	}

	//Map<Integer, Expression>
	Map<ILocation, Expression> getAnnotationMap(String procName) {
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