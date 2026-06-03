package de.uni_freiburg.informatik.ultimate.civlizer;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.WitnessGhostUpdate;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.WitnessInvariant;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.OwickiGriesAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;

class ProgramAndProof {

	private Unit mBoogieAst = null;
	private BoogieIcfgContainer mIcfg = null;
	private List<OwickiGriesAnnotation> mProof = null;
	private Map<ILocation, Set<CallStatement>> mGhostUpdateMap = null;
	// private final Map<ILocation, Set<Expression>> mAnnotationMap = null;
	private ThreadTemplateVisitor mTemplateVisitor = null;

	ProgramAndProof() {
	}

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

	void setBoogieAst(final Unit boogieAst) {
		mBoogieAst = boogieAst;
	}

	void setIcfg(final BoogieIcfgContainer icfg) {
		mIcfg = icfg;
	}

	void setProof(final List<OwickiGriesAnnotation> proof) {
		mProof = proof;
	}

	boolean isFull() {
		return mBoogieAst != null && mIcfg != null && mProof != null;
	}

	Map<ILocation, Set<CallStatement>> getGhostUpdateMap() {
		return mGhostUpdateMap;
	}

	void computeEntryAnnotationMap() {
		mEntryAnnotationMap = new HashMap<>();

		for (final BoogieIcfgLocation loc : mIcfg.getProgramPoints().get(procName).values()) {
			final var invariant = (WitnessInvariant.getAnnotation(loc) != null)
					? (Expression) WitnessInvariant.getAnnotation(loc).getInvariant()
					: null;
			final var codeLocation = ILocation.getAnnotation(loc);
			System.out.println();
			System.out.println("Invariant : " + invariant);
			System.out.println("Location : " + codeLocation);
			System.out.println(loc.getBoogieASTNode());
			result.put(codeLocation, invariant);
		}

		return result;
	}

	void computeExitAnnotationMap() {
		mExitAnnotationMap = new HashMap<>();

		for (final BoogieIcfgLocation loc : mIcfg.getProgramPoints().get(procName).values()) {
			final var invariant = (WitnessInvariant.getAnnotation(loc) != null)
					? (Expression) WitnessInvariant.getAnnotation(loc).getInvariant()
					: null;
			final var codeLocation = ILocation.getAnnotation(loc);
			System.out.println();
			System.out.println("Invariant : " + invariant);
			System.out.println("Location : " + codeLocation);
			System.out.println(loc.getBoogieASTNode());
			result.put(codeLocation, invariant);
		}

		return result;
	}

	void preprocess() {
		mTemplateVisitor = new ThreadTemplateVisitor(mBoogieAst, mIcfg);
		mGhostUpdateMap = new HashMap<>();

		// improve readability TODO

		final var programPoints = mIcfg.getProgramPoints();

		for (final Map<?, BoogieIcfgLocation> innerMap : programPoints.values()) {
			for (final BoogieIcfgLocation location : innerMap.values()) {

				for (final var edge : location.getOutgoingEdges()) {
					if (WitnessGhostUpdate.getAnnotation(edge) != null) {

						final Set<CallStatement> assignments = new HashSet<>();
						final ILocation loc = ILocation.getAnnotation(edge);

						System.out.println();
						System.out.println("Location : " + loc);
						System.out.println("Edge : " + edge);

						if (loc != null) {
							final Map<?, ?> update = WitnessGhostUpdate.getAnnotation(edge).getUpdate();

							// TODO improve readability

							for (final Map.Entry<?, ?> updateEntry : update.entrySet()) {
								System.out.println(updateEntry.getKey());
								System.out.println(updateEntry.getValue());

								final IntegerLiteral layerNum = new IntegerLiteral(loc, "2");

								final CallStatement assign = new CallStatement(loc,
										new NamedAttribute[] {
												new NamedAttribute(loc, "layer", new Expression[] { layerNum }) },
										false,
										new VariableLHS[] { new VariableLHS(loc, updateEntry.getKey().toString()) },
										"Copy", new Expression[] { (Expression) updateEntry.getValue() });
								assignments.add(assign);
							}
							mGhostUpdateMap.put(loc, assignments);
						}
					}
				}
			}
		}
	}

	// Map<Integer, Expression>
	Map<ILocation, Expression> getAnnotationMap(final String procName) {
		final Map<ILocation, Expression> result = new HashMap<>();
		for (final BoogieIcfgLocation loc : mIcfg.getProgramPoints().get(procName).values()) {
			final var invariant = (WitnessInvariant.getAnnotation(loc) != null)
					? (Expression) WitnessInvariant.getAnnotation(loc).getInvariant()
					: null;

			final var codeLocation = ILocation.getAnnotation(loc);
			// merge together
			if (result.get(codeLocation) != null) {
				final Expression buf = result.get(codeLocation);
				result.put(codeLocation,
						new BinaryExpression(codeLocation, BinaryExpression.Operator.LOGICAND, invariant, buf));
			} else {
				result.put(codeLocation, invariant);
			}

			System.out.println();
			System.out.println("Invariant : " + invariant);
			System.out.println("Location : " + codeLocation);
			System.out.println(loc.getBoogieASTNode());
		}

		return result;
	}
}