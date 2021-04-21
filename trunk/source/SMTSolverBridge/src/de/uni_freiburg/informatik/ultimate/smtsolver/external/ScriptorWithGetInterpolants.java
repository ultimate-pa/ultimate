/*
 * Copyright (C) 2015-2021 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2021 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2021 University of Freiburg
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
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Subclass of Scriptor that has support for the not yet standardized get-interpolants command. Supports iZ3, Princess,
 * and Mathsat.
 *
 * @author Matthias Heizmann
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class ScriptorWithGetInterpolants extends Scriptor {

	public enum ExternalInterpolator {
		IZ3, PRINCESS, SMTINTERPOL, MATHSAT
	}

	private final IInterpolationAdapter mInterpolationAdapter;

	public ScriptorWithGetInterpolants(final String command, final ILogger logger,
			final IUltimateServiceProvider services, final ExternalInterpolator externalInterpolator, final String name,
			final String fullPathOfDumpedFile) throws IOException {
		super(command, logger, services, name, fullPathOfDumpedFile);
		mInterpolationAdapter = createAdapter(externalInterpolator);
	}

	private IInterpolationAdapter createAdapter(final ExternalInterpolator interpolator) {
		switch (interpolator) {
		case IZ3:
			return new Z3Interpolation();
		case MATHSAT:
			return new MathsatInterpolation();
		case PRINCESS:
		case SMTINTERPOL:
			return new SmtInterpolInterpolation();
		default:
			break;
		}
		throw new AssertionError("Unknown ExternalInterpolator: " + interpolator);
	}

	@Override
	public Term[] getInterpolants(final Term[] partition) throws SMTLIBException {
		return mInterpolationAdapter.getInterpolants(partition);
	}

	@Override
	public Term[] getInterpolants(final Term[] partition, final int[] startOfSubtree) throws SMTLIBException {
		return mInterpolationAdapter.getInterpolants(partition, startOfSubtree);
	}

	@Override
	public LBool assertTerm(final Term term) throws SMTLIBException {
		return mInterpolationAdapter.assertTerm(term);
	}

	private Executor getExecutor() {
		return super.mExecutor;
	}

	private static String buildInterpolationCommand(final String initialCommand, final Term[] partition) {
		final StringBuilder command = new StringBuilder();
		final PrintTerm pt = new PrintTerm();
		command.append(initialCommand);
		String sep = "";
		for (final Term t : partition) {
			command.append(sep);
			pt.append(command, t);
			sep = " ";
		}
		command.append(")");
		return command.toString();
	}

	private static String buildInterpolationCommand(final String initialCommand, final Term[] partition,
			final int[] startOfSubtree) {
		final StringBuilder command = new StringBuilder();
		final PrintTerm pt = new PrintTerm();
		command.append(initialCommand);
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
		return command.toString();
	}

	private interface IInterpolationAdapter {
		Term[] getInterpolants(final Term[] partition) throws SMTLIBException, UnsupportedOperationException;

		Term[] getInterpolants(final Term[] partition, final int[] startOfSubtree)
				throws SMTLIBException, UnsupportedOperationException;

		LBool assertTerm(final Term term) throws SMTLIBException;

	}

	private final class SmtInterpolInterpolation implements IInterpolationAdapter {

		private static final String CMD = "(get-interpolants ";

		@Override
		public Term[] getInterpolants(final Term[] partition) throws SMTLIBException, UnsupportedOperationException {
			sendInterpolationCommand(partition);
			return readInterpolants();
		}

		@Override
		public Term[] getInterpolants(final Term[] partition, final int[] startOfSubtree) throws SMTLIBException {
			sendInterpolationCommand(partition, startOfSubtree);
			return readInterpolants();
		}

		@Override
		public LBool assertTerm(final Term term) throws SMTLIBException {
			return ScriptorWithGetInterpolants.super.assertTerm(term);
		}

		private void sendInterpolationCommand(final Term[] partition) {
			final String command = buildInterpolationCommand(CMD, partition);
			getExecutor().input(command);
		}

		private void sendInterpolationCommand(final Term[] partition, final int[] startOfSubtree) {
			final String command = buildInterpolationCommand(CMD, partition, startOfSubtree);
			getExecutor().input(command);
		}

		private Term[] readInterpolants() {
			return ScriptorWithGetInterpolants.super.mExecutor.parseGetAssertionsResult();
		}
	}

	private final class Z3Interpolation implements IInterpolationAdapter {

		private static final String CMD = "(get-interpolant ";

		@Override
		public Term[] getInterpolants(final Term[] partition) throws SMTLIBException {
			sendInterpolationCommand(partition);
			return readInterpolants();
		}

		@Override
		public Term[] getInterpolants(final Term[] partition, final int[] startOfSubtree) throws SMTLIBException {
			sendInterpolationCommand(partition, startOfSubtree);
			return readInterpolants();
		}

		@Override
		public LBool assertTerm(final Term term) throws SMTLIBException {
			return ScriptorWithGetInterpolants.super.assertTerm(term);
		}

		private void sendInterpolationCommand(final Term[] partition) {
			final String command = buildInterpolationCommand(CMD, partition);
			getExecutor().input(command);
		}

		private void sendInterpolationCommand(final Term[] partition, final int[] startOfSubtree) {
			final String command = buildInterpolationCommand(CMD, partition, startOfSubtree);
			getExecutor().input(command);
		}

		private Term[] readInterpolants() {
			return ScriptorWithGetInterpolants.super.mExecutor.parseInterpolants();
		}
	}

	private final class MathsatInterpolation implements IInterpolationAdapter {

		private static final String CMD = "(get-interpolant (";

		@Override
		public Term[] getInterpolants(final Term[] partition) throws SMTLIBException {
			final List<Term> currentA = new ArrayList<>();
			final List<Term> interpolants = new ArrayList<>();
			for (int i = 0; i < partition.length; ++i) {
				final List<Term> current = flatten(partition[i]);
				currentA.addAll(current);
				sendInterpolationCommand(currentA.toArray(new Term[currentA.size()]));
				interpolants.addAll(Arrays.asList(readInterpolants()));
			}
			return interpolants.toArray(new Term[interpolants.size()]);
		}

		@Override
		public Term[] getInterpolants(final Term[] partition, final int[] startOfSubtree) throws SMTLIBException {
			throw new UnsupportedOperationException("Not yet implemented");
		}

		@Override
		public LBool assertTerm(final Term term) throws SMTLIBException {
			final Term actualTerm = convertAnnotationNamedToInterpolationGroup(term);
			return ScriptorWithGetInterpolants.super.assertTerm(actualTerm);
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

		private void sendInterpolationCommand(final Term[] partition) {
			final StringBuilder command = new StringBuilder();
			final PrintTerm pt = new PrintTerm();
			command.append(CMD);
			String sep = "";
			for (final Term t : partition) {
				command.append(sep);
				pt.append(command, t);
				sep = " ";
			}
			command.append("))");

			getExecutor().input(command.toString());
		}

		private void sendInterpolationCommand(final Term[] partition, final int[] startOfSubtree) {
			final String command = buildInterpolationCommand(CMD, partition, startOfSubtree);
			getExecutor().input(command);
		}

		private Term readInterpolants() {
			return ScriptorWithGetInterpolants.super.mExecutor.parseTerm();
		}

		private List<Term> flatten(final Term t) {
			if (t instanceof ApplicationTerm) {
				final ApplicationTerm aTerm = (ApplicationTerm) t;
				if ("and".equals(aTerm.getFunction().getName())) {
					return Arrays.asList(aTerm.getParameters());
				}
			}
			return Collections.singletonList(t);
		}

	}

}
