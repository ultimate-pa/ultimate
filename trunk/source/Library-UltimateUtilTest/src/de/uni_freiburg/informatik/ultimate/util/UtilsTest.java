package de.uni_freiburg.informatik.ultimate.util;

import org.junit.Assert;

import org.junit.Test;

public class UtilsTest {
	
	@Test
	public void HumanReadableBytesTest(){
		Assert.assertEquals("1 B", Utils.humanReadableByteCount(1, false));
		Assert.assertEquals("1000 B", Utils.humanReadableByteCount(1000, false));
		Assert.assertEquals("1.0 KiB", Utils.humanReadableByteCount(1024, false));
		Assert.assertEquals("1.0 kB", Utils.humanReadableByteCount(1000, true));
		Assert.assertEquals("9.2 EB", Utils.humanReadableByteCount(Long.MAX_VALUE, true));
		Assert.assertEquals(Long.MIN_VALUE+" B", Utils.humanReadableByteCount(Long.MIN_VALUE, true));
		Assert.assertEquals("8.0 EiB", Utils.humanReadableByteCount(Long.MAX_VALUE, false));
		Assert.assertEquals(Long.MIN_VALUE+" B", Utils.humanReadableByteCount(Long.MIN_VALUE, false));
		Assert.assertEquals("0 B", Utils.humanReadableByteCount(0, true));
		Assert.assertEquals("0 B", Utils.humanReadableByteCount(0, false));
		Assert.assertEquals("1.0 MiB", Utils.humanReadableByteCount(1048576, false));
	}
}
