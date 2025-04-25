/*
 * Copyright (C) 2024 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2025 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024-2025 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import java.math.BigInteger;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.ICType;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLPrettyPrinter;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Expression;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BigInterval;

/**
 * Represents a value resulting from the backtranslation from Boogie to C/ACSL.
 */
public sealed interface BacktranslatedACSLValue {
	/**
	 * Represents a backtranslated value in the form of an ACSL expression.
	 *
	 * Such expressions may be used for the backtranslation of invariants and procedure contracts, as well as for
	 * program states.
	 */
	public record BacktranslatedExpression(Expression expression, ICType cType, BigInterval range)
			implements BacktranslatedACSLValue {
		public BacktranslatedExpression(final Expression expression) {
			this(expression, null, BigInterval.unbounded());
		}

		public BacktranslatedExpression {
			Objects.requireNonNull(expression);
			Objects.requireNonNull(range);
			// cType is allowed to be null
		}

		@Override
		public String toString() {
			return ACSLPrettyPrinter.print(expression);
		}
	}

	/**
	 * Represents a backtranslated value for a memory address in our memory model, consisting of a base address and an
	 * offset.
	 *
	 * This is not a real ACSL expression, and should only be used in the backtranslation of program states, not in
	 * invariants or contracts. Moreover, it must only be used for the values in a program state, not as a key (it does
	 * not represent a variable).
	 *
	 * While these values do not make sense outside of our tool (and thus should never make it into witnesses etc), they
	 * can be used for log output and can be helpful when debugging a feasible error trace reported by Ultimate.
	 */
	public record FakePointer(BigInteger base, BigInteger offset) implements BacktranslatedACSLValue {
		public FakePointer {
			Objects.requireNonNull(base);
			Objects.requireNonNull(offset);
		}

		@Override
		public String toString() {
			return "{%s:%s}".formatted(base, offset);
		}
	}
}
