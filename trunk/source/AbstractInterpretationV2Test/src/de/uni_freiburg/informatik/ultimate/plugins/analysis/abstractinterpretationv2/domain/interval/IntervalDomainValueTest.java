package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.interval;

import static org.junit.Assert.*;

import java.math.BigDecimal;

import org.junit.Test;

public class IntervalDomainValueTest {

	@Test
	public void testInfiniteIntervalValue() {

		IntervalValue infiniteValue = new IntervalValue();
		assertTrue(infiniteValue.getValue() == null);
		assertTrue(infiniteValue.isInfinity());
	}

	@Test
	public void testBoundedIntervalValue() {
		IntervalValue intv = new IntervalValue(new BigDecimal(0));

		assertTrue(intv.getValue().equals(new BigDecimal(0)));
		assertFalse(intv.isInfinity());

		IntervalValue intvNeg = new IntervalValue(new BigDecimal(-1));
		assertTrue(intvNeg.getValue().equals(new BigDecimal(-1)));
		assertFalse(intvNeg.isInfinity());

		IntervalValue intvPos = new IntervalValue(new BigDecimal(1));
		assertTrue(intvPos.getValue().equals(new BigDecimal(1)));
		assertFalse(intvPos.isInfinity());
	}

	@Test
	public void testInfiniteInterval() {
		IntervalDomainValue intv = new IntervalDomainValue();

		assertTrue(intv.getUpper().equals(new IntervalValue()));
		assertTrue(intv.getUpper().isInfinity());
		assertTrue(intv.getLower().equals(new IntervalValue()));
		assertTrue(intv.getLower().isInfinity());
	}

	@Test
	public void testBoundedInterval() {
		IntervalDomainValue intvUpperOpen = new IntervalDomainValue(new IntervalValue(new BigDecimal(0)),
		        new IntervalValue());

		assertFalse(intvUpperOpen.getLower().isInfinity());
		assertTrue(intvUpperOpen.getUpper().isInfinity());

		IntervalDomainValue intvLowerOpen = new IntervalDomainValue(new IntervalValue(), new IntervalValue(
		        new BigDecimal(100)));

		assertTrue(intvLowerOpen.getLower().isInfinity());
		assertFalse(intvLowerOpen.getUpper().isInfinity());
	}

	@Test
	public void testBottomIntervals() {
		IntervalDomainValue bottomInterval = new IntervalDomainValue(true);
		assertTrue(bottomInterval.isBottom());
		assertTrue(bottomInterval.getLower() == null);
		assertTrue(bottomInterval.getUpper() == null);

		IntervalDomainValue normalInterval = new IntervalDomainValue(new IntervalValue(new BigDecimal(1)),
		        new IntervalValue(new BigDecimal(10)));
	}
}
