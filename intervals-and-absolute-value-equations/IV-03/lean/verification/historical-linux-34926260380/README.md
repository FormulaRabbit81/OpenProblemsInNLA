# Authenticated historical IV-03 execution

This directory preserves the successful historical run from Sidney Holden's
repository. It is distinct from the pending fresh verification of the campaign
integration commit.

- Run: [34926260380](https://github.com/sidneyholden1/OpenProblemsInNLA/actions/runs/34926260380).
- Actual tested commit: `516ad4a0e85c21c7ef34507db9ab3b68b393bb90`.
- Verification job: `104244928525`.
- Artifact: `10380345663`, original [ZIP](lean-IV-03.zip).
- ZIP SHA-256: `bef757bd594f82e327625b5bcbcc3c395e6d64e3764c95f926a25ffe95337177`.
- [Result receipt](artifact/verify-20260915T034753Z-4053/result.json) SHA-256:
  `50494ef3df157aa2b69cdbc6c9f6a00d568be6d64e80678686be974f0393bfa7`.

The [identity summary](API-IDENTITY-SUMMARY.json) is explicitly derived from
authenticated GitHub API responses and records their original SHA-256 hashes.
It is not a raw response. Raw run/commit API records are omitted because they
can include contact-email metadata. The ZIP, extracted artifact members and
[verification job log](job-104244928525.log) are unchanged. They were scanned
before packaging and contain no contact-email matches.

The actual Comparator output builds the separate Challenge and complete
thirteen-file Solution closure. All four exports passed Lean's default-kernel
replay, Comparator and LeanCert kernel-trust assertions using only `propext`,
`Classical.choice`, and `Quot.sound`. The original 75 receipt inputs are bound
to the exact tested Git revision in both campaign reviews. All fourteen active
Lean files equal the later imported source revision; only the later source
README and formalization metadata differ from the tested project.

The logs contain the honest kernel acceptance, invalid raw proof rejection,
quotient post-check rejection, all five Comparator regressions, deliberate
`sorryAx` and native-axiom rejections, and the nonroot build/export sandbox
controls. A separately skipped controls job does not substitute for these
actual per-project commands, which ran and passed in the verification job.
Both campaign referees checked the logs against the actual GitHub job stream.

These are authenticated records of an earlier Linux execution. Packaging them
does not run Lean again, make the checker infallible, or complete the new
campaign's verification gate.
