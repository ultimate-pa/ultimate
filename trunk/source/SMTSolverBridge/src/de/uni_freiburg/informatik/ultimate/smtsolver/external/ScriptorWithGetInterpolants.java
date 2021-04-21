/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE SMTSolverBridge.
 *
 * The ULTIMATE SMTSolverBridge is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE SMTSolverBridge is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SMTSolverBridge. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SMTSolverBridge, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE SMTSolverBridge grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.smtsolver.external;

import java.io.IOException;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Subclass of Scriptor that has support for the not yet standardized get-interpolants command. Supports iZ3 and
 * Princess.
 *
 * @author Matthias Heizmann
 *
 */
public class ScriptorWithGetInterpolants extends Scriptor {

	public enum ExternalInterpolator {
		IZ3, PRINCESS, SMTINTERPOL, MATHSAT
	}

	private final ExternalInterpolator mExternalInterpolator;

	public ScriptorWithGetInterpolants(final String command, final ILogger logger,
			final IUltimateServiceProvider services, final ExternalInterpolator externalInterpolator, final String name,
			final String fullPathOfDumpedFile) throws IOException {
		super(command, logger, services, name, fullPathOfDumpedFile);
		mExternalInterpolator = externalInterpolator;
	}

	@Override
	public Term[] getInterpolants(final Term[] partition) throws SMTLIBException, UnsupportedOperationException {
		sendInterpolationCommand(partition);
		return readInterpolants();
	}

	@Override
	public Term[] getInterpolants(final Term[] partition, final int[] startOfSubtree)
			throws SMTLIBException, UnsupportedOperationException {
		sendInterpolationCommand(partition, startOfSubtree);
		return readInterpolants();
	}

	@Override
	public LBool assertTerm(final Term term) throws SMTLIBException {
		final Term actualTerm;
		if (mExternalInterpolator == ExternalInterpolator.MATHSAT) {
			actualTerm = convertAnnotationNamedToInterpolationGroup(term);
		} else {
			actualTerm = term;
		}
		return super.assertTerm(actualTerm);
	}

	private Term convertAnnotationNamedToInterpolationGroup(final Term term) {
		if (term instanceof AnnotatedTerm) {
			final AnnotatedTerm aterm = (AnnotatedTerm) term;
			final Annotation[] annots = aterm.getAnnotations();
			final Annotation[] newAnnots = new Annotation[annots.length];
			boolean changed = false;
			for (int i = 0; i < annots.length; ++i) {
				final Annotation annot = annots[i];
				if (":named".equals(annot.getKey())) {
					changed = true;
					newAnnots[i] = new Annotation(":interpolation-group", annot.getValue());
				} else {
					newAnnots[i] = annot;
				}
			}
			if (changed) {
				return annotate(aterm.getSubterm(), newAnnots);
			}
		}
		return term;
	}

	private void sendInterpolationCommand(final Term[] partition) throws AssertionError {
		final StringBuilder command = new StringBuilder();
		final PrintTerm pt = new PrintTerm();
		switch (mExternalInterpolator) {
		case IZ3:
		case MATHSAT:
			command.append("(get-interpolant ");
			break;
		case PRINCESS:
		case SMTINTERPOL:
			command.append("(get-interpolants ");
			break;
		default:
			throw new AssertionError("unknown ExternalInterpolator: " + mExternalInterpolator);
		}
		String sep = "";
		for (final Term t : partition) {
			command.append(sep);
			pt.append(command, t);
			sep = " ";
		}
		command.append(")");
		super.mExecutor.input(command.toString());
	}

	private void sendInterpolationCommand(final Term[] partition, final int[] startOfSubtree) throws AssertionError {
		final StringBuilder command = new StringBuilder();
		final PrintTerm pt = new PrintTerm();
		switch (mExternalInterpolator) {
		case IZ3:
		case MATHSAT:
			command.append("(get-interpolant ");
			break;
		case PRINCESS:
		case SMTINTERPOL:
			command.append("(get-interpolants ");
			break;
		default:
			throw new AssertionError("unknown ExternalInterpolator: " + mExternalInterpolator);
		}
		pt.append(command, partition[0]);
		for (int i = 1; i < partition.length; ++i) {
			int prevStart = startOfSubtree[i - 1];
			while (startOfSubtree[i] < prevStart) {
				command.append(')');
				prevStart = startOfSubtree[prevStart - 1];
			}
			command.append(' ');
			if (startOfSubtree[i] == i) {
				command.append('(');
			}
			pt.append(command, partition[i]);
		}
		command.append(')');
		super.mExecutor.input(command.toString());
	}

	private Term[] readInterpolants() throws AssertionError {
		Term[] interpolants;
		switch (mExternalInterpolator) {
		case IZ3:
			interpolants = super.mExecutor.parseInterpolants();
			break;
		case MATHSAT:
		case PRINCESS:
		case SMTINTERPOL:
			interpolants = super.mExecutor.parseGetAssertionsResult();
			break;
		default:
			throw new AssertionError("unknown ExternalInterpolator: " + mExternalInterpolator);
		}
		return interpolants;
	}

}
