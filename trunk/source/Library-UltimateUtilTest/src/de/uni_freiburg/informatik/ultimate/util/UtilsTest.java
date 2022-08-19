/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Util Library.
 *
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Util Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util;

import java.util.Locale;
import java.util.concurrent.TimeUnit;

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

public class UtilsTest {

	private Locale mDefault;

	@Before
	public void setup() {
		mDefault = Locale.getDefault();
		Locale.setDefault(Locale.US);
	}

	@After
	public void tearDown() {
		Locale.setDefault(mDefault);
	}

	@Test
	public void humanReadableBytesTest() {
		Assert.assertEquals("1B", CoreUtil.humanReadableByteCount(1, false));
		Assert.assertEquals("1000B", CoreUtil.humanReadableByteCount(1000, false));
		Assert.assertEquals("1.0KiB", CoreUtil.humanReadableByteCount(1024, false));
		Assert.assertEquals("1.0kB", CoreUtil.humanReadableByteCount(1000, true));
		Assert.assertEquals("9.2EB", CoreUtil.humanReadableByteCount(Long.MAX_VALUE, true));
		Assert.assertEquals(Long.MIN_VALUE + "B", CoreUtil.humanReadableByteCount(Long.MIN_VALUE, true));
		Assert.assertEquals("8.0EiB", CoreUtil.humanReadableByteCount(Long.MAX_VALUE, false));
		Assert.assertEquals(Long.MIN_VALUE + "B", CoreUtil.humanReadableByteCount(Long.MIN_VALUE, false));
		Assert.assertEquals("0B", CoreUtil.humanReadableByteCount(0, true));
		Assert.assertEquals("0B", CoreUtil.humanReadableByteCount(0, false));
		Assert.assertEquals("1.0MiB", CoreUtil.humanReadableByteCount(1048576, false));
	}

	@Test
	public void humanReadableTimesTest() {
		Assert.assertEquals("2s", CoreUtil.humanReadableTime(2000, TimeUnit.MILLISECONDS, 0));
		Assert.assertEquals("2s", CoreUtil.humanReadableTime(2400, TimeUnit.MILLISECONDS, 0));
		Assert.assertEquals("2.4s", CoreUtil.humanReadableTime(2400, TimeUnit.MILLISECONDS, 1));
		Assert.assertEquals("1.0h", CoreUtil.humanReadableTime(3600, TimeUnit.SECONDS, 1));
		Assert.assertEquals("1.0d", CoreUtil.humanReadableTime(24, TimeUnit.HOURS, 1));
		Assert.assertEquals("2d", CoreUtil.humanReadableTime(2, TimeUnit.DAYS, 0));
	}

	@Test(expected = Test.None.class)
	public void timestamps() {
		final String isoTimeStamp = CoreUtil.getIsoUtcTimestamp();
		System.out.println("Now without offset: " + isoTimeStamp);
	}

	@Test(expected = Test.None.class)
	public void timestampsWithOffset() {
		final String isoTimeStamp = CoreUtil.getIsoUtcTimestampWithUtcOffset();
		System.out.println("Now with offset: " + isoTimeStamp);
	}

}
