import { AbsoluteFill, Easing, interpolate, useCurrentFrame, useVideoConfig } from "remotion";
import { BODY, CYAN, GOLD, HEAD } from "../theme";

const clamp = { extrapolateLeft: "clamp", extrapolateRight: "clamp" } as const;

/** One huge word slammed onto the beat. */
export const Slam: React.FC<{ readonly text: string; readonly color?: string; readonly size?: number }> = ({ text, color = "white", size = 190 }) => {
  const frame = useCurrentFrame();
  const { durationInFrames } = useVideoConfig();
  return (
    <AbsoluteFill style={{ justifyContent: "center", alignItems: "center" }}>
      <div
        style={{
          fontFamily: HEAD,
          fontWeight: 900,
          fontSize: size,
          letterSpacing: interpolate(frame, [0, durationInFrames], [6, 26], clamp),
          color,
          textShadow: `0 0 40px ${CYAN}aa, 0 0 6px #fff, 0 8px 30px #000`,
          scale: interpolate(frame, [0, 7], [1.7, 1], { ...clamp, easing: Easing.bezier(0.1, 0.9, 0.2, 1) }),
          filter: `blur(${interpolate(frame, [0, 6], [14, 0], clamp)}px)`,
          opacity: interpolate(frame, [0, 3, durationInFrames - 6, durationInFrames], [0, 1, 1, 0], clamp),
        }}
      >
        {text}
      </div>
    </AbsoluteFill>
  );
};

/** Section headline: small kicker + big line, bottom-left, slides in. */
export const Headline: React.FC<{ readonly kicker?: string; readonly text: string; readonly color?: string }> = ({ kicker, text, color = CYAN }) => {
  const frame = useCurrentFrame();
  const { durationInFrames } = useVideoConfig();
  const out = interpolate(frame, [durationInFrames - 8, durationInFrames], [1, 0], clamp);
  return (
    <AbsoluteFill style={{ justifyContent: "flex-end", padding: "0 0 120px 130px" }}>
      <AbsoluteFill style={{ opacity: out * interpolate(frame, [0, 8], [0, 1], clamp), background: "linear-gradient(0deg, rgba(2,4,12,.88) 0%, rgba(2,4,12,.55) 26%, rgba(2,4,12,0) 46%)" }} />
      <div style={{ opacity: out, position: "relative" }}>
        {kicker ? (
          <div
            style={{
              fontFamily: BODY,
              fontWeight: 700,
              fontSize: 40,
              letterSpacing: 8,
              color: GOLD,
              textTransform: "uppercase",
              textShadow: "0 2px 12px #000",
              translate: interpolate(frame, [2, 14], ["-40px 0px", "0px 0px"], { ...clamp, easing: Easing.bezier(0.16, 1, 0.3, 1) }),
              opacity: interpolate(frame, [2, 10], [0, 1], clamp),
            }}
          >
            {kicker}
          </div>
        ) : null}
        <div style={{ display: "flex", alignItems: "center", gap: 26 }}>
          <div style={{ width: 10, height: 96, background: color, boxShadow: `0 0 24px ${color}`, scale: `1 ${interpolate(frame, [0, 8], [0, 1], { ...clamp, easing: Easing.bezier(0.16, 1, 0.3, 1) })}` }} />
          <div
            style={{
              fontFamily: HEAD,
              fontWeight: 900,
              fontSize: 92,
              color: "white",
              lineHeight: 1,
              textShadow: `0 0 30px ${color}88, 0 6px 26px #000`,
              clipPath: `inset(0 ${interpolate(frame, [4, 18], [100, 0], { ...clamp, easing: Easing.bezier(0.16, 1, 0.3, 1) })}% 0 0)`,
            }}
          >
            {text}
          </div>
        </div>
      </div>
    </AbsoluteFill>
  );
};

/** System lower-third: "SISTEMA 7 / 15" + name, top-left. */
export const SystemTag: React.FC<{ readonly n: number; readonly name: string; readonly sub?: string; readonly color?: string }> = ({ n, name, sub, color = CYAN }) => {
  const frame = useCurrentFrame();
  const { durationInFrames } = useVideoConfig();
  return (
    <AbsoluteFill style={{ padding: "110px 0 0 130px" }}>
      <div style={{ opacity: interpolate(frame, [0, 4, durationInFrames - 4, durationInFrames], [0, 1, 1, 0], clamp) }}>
        <div style={{ fontFamily: BODY, fontWeight: 700, fontSize: 34, letterSpacing: 7, color, textShadow: "0 2px 10px #000" }}>
          SISTEMA {n} / 15
        </div>
        <div
          style={{
            fontFamily: HEAD,
            fontWeight: 900,
            fontSize: 84,
            color: "white",
            textShadow: `0 0 26px ${color}99, 0 6px 22px #000`,
            translate: interpolate(frame, [0, 10], ["-30px 0px", "0px 0px"], { ...clamp, easing: Easing.bezier(0.16, 1, 0.3, 1) }),
          }}
        >
          {name}
        </div>
        {sub ? <div style={{ fontFamily: BODY, fontWeight: 600, fontSize: 38, color: "#dfe8ff", textShadow: "0 2px 10px #000" }}>{sub}</div> : null}
      </div>
    </AbsoluteFill>
  );
};

/** Centered sentence revealed word by word (for quiet moments). */
export const Line: React.FC<{ readonly text: string; readonly size?: number; readonly color?: string; readonly stagger?: number }> = ({ text, size = 78, color = "white", stagger = 5 }) => {
  const frame = useCurrentFrame();
  const { durationInFrames } = useVideoConfig();
  const words = text.split(" ");
  return (
    <AbsoluteFill style={{ justifyContent: "center", alignItems: "center", padding: "0 160px" }}>
      <div style={{ display: "flex", flexWrap: "wrap", justifyContent: "center", gap: "0 26px", opacity: interpolate(frame, [durationInFrames - 8, durationInFrames], [1, 0], clamp) }}>
        {words.map((w, i) => (
          <span
            key={i}
            style={{
              fontFamily: HEAD,
              fontWeight: 700,
              fontSize: size,
              color,
              textShadow: "0 0 26px rgba(61,232,255,.45), 0 6px 24px #000",
              opacity: interpolate(frame, [i * stagger, i * stagger + 8], [0, 1], clamp),
              translate: interpolate(frame, [i * stagger, i * stagger + 12], ["0px 24px", "0px 0px"], { ...clamp, easing: Easing.bezier(0.16, 1, 0.3, 1) }),
              filter: `blur(${interpolate(frame, [i * stagger, i * stagger + 8], [8, 0], clamp)}px)`,
            }}
          >
            {w}
          </span>
        ))}
      </div>
    </AbsoluteFill>
  );
};
