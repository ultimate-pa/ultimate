package de.uni_freiburg.informatik.ultimate.core.lib.results.dto.simple;

import java.io.Serializable;
import java.util.Date;

import com.google.gson.annotations.SerializedName;

@SuppressWarnings("serial")
public final class SimpleDTO implements Serializable {

	@SerializedName("time")
	final Date mTime;

	@SerializedName("ultimate")
	final Content mUltimate;

	public SimpleDTO(final Date time, final Content ultimate) {
		mTime = time;
		mUltimate = ultimate;
	}

	public Date getTime() {
		return mTime;
	}

	public Content getUltimate() {
		return mUltimate;
	}
}
