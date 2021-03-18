package de.uni_freiburg.informatik.ultimate.lib.pea.test;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

import org.hamcrest.MatcherAssert;
import org.hamcrest.core.Is;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
@RunWith(Parameterized.class)
public class CddTest {

	private final TestData mData;
	private final ILogger mLogger;

	public CddTest(final TestData data) {
		mData = data;
		final IUltimateServiceProvider services = UltimateMocks.createUltimateServiceProviderMock();
		mLogger = services.getLoggingService().getLogger(getClass());
	}

	@Test
	public void testToString() {
		mLogger.info("********************************* CDD ********************************* ");
		mLogger.info(mData.mCdd.toString());
		mLogger.info(mData.mCdd.toTexString());
	}

	@Test
	public void testIsAtomic() {
		MatcherAssert.assertThat(mData.mCdd.toString(), mData.mCdd.isAtomic(), Is.is(mData.mIsAtomic));
	}

	@Test
	public void testToDnf() {
		final CDD[] dnf = mData.mCdd.toDNF();
		mLogger.info("********************************* DNF ********************************* ");
		for (int i = 0; i < dnf.length; i++) {
			mLogger.info("Conjunct %d : %s", i, dnf[i]);
		}
	}

	@Test
	public void testToCnf() {
		final CDD[] cnf = mData.mCdd.toCNF();
		mLogger.info("********************************* CNF ********************************* ");
		for (int i = 0; i < cnf.length; i++) {
			mLogger.info("Disjunct %d : %s", i, cnf[i]);
		}
	}

	@Parameters(name = "{index}: {0}")
	public static Collection<Object[]> data() {
		final CDD a = BooleanDecision.create("a");
		final CDD b = BooleanDecision.create("b");
		final CDD c = BooleanDecision.create("c");
		final CDD d = BooleanDecision.create("d");

		final List<TestData> data = new ArrayList<>();
		final CDD left = a.negate().and(b);
		final CDD right = a.and(b.or(c)).and(d);
		data.add(new TestData(left, false));
		data.add(new TestData(right, false));
		data.add(new TestData(left.or(right), false));
		data.add(new TestData(a.negate(), true));
		data.add(new TestData(a.or(b), false));
		return data.stream().map(TestData::toData).collect(Collectors.toList());
	}

	private static final class TestData {
		private final CDD mCdd;
		private final boolean mIsAtomic;

		public TestData(final CDD cdd, final boolean isAtomic) {
			mCdd = cdd;
			mIsAtomic = isAtomic;
		}

		private Object[] toData() {
			return new Object[] { this };
		}

		@Override
		public String toString() {
			return mCdd.toString();
		}
	}
}
