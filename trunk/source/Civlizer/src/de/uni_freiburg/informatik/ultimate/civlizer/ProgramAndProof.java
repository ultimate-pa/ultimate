/*
 * Copyright (C) 2026 Dominik Klumpp (klumpp@lix.polytechnique.fr)
 * Copyright (C) 2026 École Polytechnique
 *
 * This file is part of the ULTIMATE Civlizer plug-in.
 *
 * The ULTIMATE Civlizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Civlizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Civlizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Civlizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Civlizer plug-in grant you additional permission
 * to convey the resulting work.
 */
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
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.WitnessGhostUpdate;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.WitnessInvariant;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.OwickiGriesAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;

/**
 * Internal container that bundles together the Boogie AST, the generated ICFG, and the associated proof information.
 *
 * <p>
 * It also computes derived structures such as ghost update mappings and annotation maps extracted from the ICFC and
 * witness annotations.
 * </p>
 */
final class ProgramAndProof {

	private Unit mBoogieAst = null;
	private BoogieIcfgContainer mIcfg = null;
	private List<OwickiGriesAnnotation> mProof = null;
	private Map<ILocation, Set<CallStatement>> mGhostUpdateMap = null;
	// private final Map<ILocation, Set<Expression>> mAnnotationMap = null;
	private ThreadTemplateVisitor mTemplateVisitor = null;

	private BoogieStatementIdMap mStatementIdMap = null;

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

	BoogieStatementIdMap getStatementIdMap() {
		return mStatementIdMap;
	}

	/**
	 * Preprocesses the ICFC to extract ghost updates and initialize auxiliary structures.
	 *
	 * <p>
	 * This method:
	 * <ul>
	 * <li>Initializes the thread template visitor</li>
	 * <li>Scans all CFG edges for {@link WitnessGhostUpdate} annotations</li>
	 * <li>Creates Boogie call statements representing ghost updates</li>
	 * <li>Stores them in {@code mGhostUpdateMap}</li>
	 * </ul>
	 * </p>
	 */
	void preprocess() {
		mTemplateVisitor = new ThreadTemplateVisitor(mBoogieAst, mIcfg);
		mGhostUpdateMap = new HashMap<>();
		mStatementIdMap = new BoogieStatementIdMap(mBoogieAst);

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

			final var codeLocation = ILocation.getAnnotation(loc);

			if (!loc.isErrorLocation() && loc.getBoogieASTNode() instanceof Statement) {

				final Expression invariant = (WitnessInvariant.getAnnotation(loc) != null)
						? (Expression) WitnessInvariant.getAnnotation(loc).getInvariant()
						: null;

				// merge together
				if (result.get(codeLocation) != null) {
					final Expression buf = result.get(codeLocation);
					result.put(codeLocation,
							new BinaryExpression(codeLocation, BinaryExpression.Operator.LOGICAND, invariant, buf));
				} else {
					result.put(codeLocation, invariant);
				}
			}

			System.out.println();
			System.out.println("Location : " + codeLocation);
			System.out.println(loc.getBoogieASTNode());
		}

		return result;
	}
}