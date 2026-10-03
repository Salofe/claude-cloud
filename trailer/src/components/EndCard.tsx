import { AbsoluteFill, Easing, interpolate, useCurrentFrame } from "remotion";
import { BODY, CYAN, GOLD, HEAD } from "../theme";

const clamp = { extrapolateLeft: "clamp", extrapolateRight: "clamp" } as const;
const ease = Easing.bezier(0.16, 1, 0.3, 1);

/** Title card: logo slam with a light sweep, tagline, where to play. */
export const EndCard: React.FC<{ readonly url: string; readonly tagline: string; readonly cta: string; readonly platforms: string; readonly vertical?: boolean }> = ({ url, tagline, cta, platforms, vertical = false }) => {
  const k = vertical ? 0.54 : 1;
  const frame = useCurrentFrame();
  const sweep = interpolate(frame, [8, 40], [-30, 130], clamp);
  return (
    <AbsoluteFill style={{ justifyContent: "center", alignItems: "center" }}>
      <AbsoluteFill style={{ background: "radial-gradient(ellipse at center, rgba(3,6,18,0.35) 0%, rgba(3,6,18,0.85) 70%)" }} />
      <div style={{ textAlign: "center", marginTop: -40 }}>
        <div
          style={{
            fontFamily: HEAD,
            fontWeight: 900,
            lineHeight: 0.95,
            scale: interpolate(frame, [0, 10], [1.35, 1], { ...clamp, easing: ease }),
            filter: `blur(${interpolate(frame, [0, 8], [16, 0], clamp)}px)`,
            opacity: interpolate(frame, [0, 4], [0, 1], clamp),
          }}
        >
          <div style={{ fontSize: 150 * k, color: "white", letterSpacing: 10 * k, textShadow: "0 0 40px rgba(255,255,255,.35)" }}>SOLAR</div>
          <div
            style={{
              fontSize: 196 * k,
              letterSpacing: 6 * k,
              color: CYAN,
              textShadow: `0 0 60px ${CYAN}, 0 0 8px #fff`,
              WebkitMaskImage: `linear-gradient(100deg, rgba(0,0,0,.82) ${sweep - 12}%, #000 ${sweep}%, rgba(0,0,0,.82) ${sweep + 12}%)`,
            }}
          >
            PROSPECTOR
          </div>
        </div>
        <div
          style={{
            marginTop: 34,
            fontFamily: BODY,
            fontWeight: 700,
            fontSize: vertical ? 40 : 50,
            letterSpacing: vertical ? 5 : 12,
            padding: vertical ? "0 60px" : 0,
            color: GOLD,
            textTransform: "uppercase",
            opacity: interpolate(frame, [14, 24], [0, 1], clamp),
            translate: interpolate(frame, [14, 28], ["0px 20px", "0px 0px"], { ...clamp, easing: ease }),
          }}
        >
          {tagline}
        </div>
        <div style={{ marginTop: 56, opacity: interpolate(frame, [30, 40], [0, 1], clamp), translate: interpolate(frame, [30, 44], ["0px 24px", "0px 0px"], { ...clamp, easing: ease }) }}>
          <div style={{ fontFamily: HEAD, fontWeight: 700, fontSize: vertical ? 52 : 54, color: "white", textShadow: "0 4px 20px #000" }}>{cta}</div>
          <div
            style={{
              display: "inline-block",
              marginTop: 22,
              padding: "16px 40px",
              borderRadius: 60,
              border: `3px solid ${CYAN}`,
              background: "rgba(10,30,50,.75)",
              boxShadow: `0 0 ${interpolate(frame % 60, [0, 30, 60], [18, 40, 18])}px ${CYAN}88`,
              fontFamily: BODY,
              fontWeight: 700,
              fontSize: vertical ? 46 : 52,
              color: CYAN,
              letterSpacing: 2,
            }}
          >
            {url}
          </div>
          <div style={{ marginTop: 22, fontFamily: BODY, fontWeight: 600, fontSize: vertical ? 36 : 40, color: "#c9d6f5", letterSpacing: vertical ? 2 : 4 }}>{platforms}</div>
        </div>
      </div>
    </AbsoluteFill>
  );
};
