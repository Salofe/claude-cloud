import { AbsoluteFill, interpolate, random, useCurrentFrame } from "remotion";

/** Vignette + animated film grain over the whole trailer. */
export const Grade: React.FC = () => {
  const frame = useCurrentFrame();
  const gx = Math.floor(random(`gx${frame}`) * 200);
  const gy = Math.floor(random(`gy${frame}`) * 200);
  return (
    <AbsoluteFill style={{ pointerEvents: "none" }}>
      <AbsoluteFill style={{ background: "radial-gradient(ellipse at center, rgba(0,0,0,0) 55%, rgba(0,0,8,0.55) 100%)" }} />
      <AbsoluteFill
        style={{
          opacity: 0.07,
          backgroundImage:
            "url(\"data:image/svg+xml;utf8,<svg xmlns='http://www.w3.org/2000/svg' width='256' height='256'><filter id='n'><feTurbulence type='fractalNoise' baseFrequency='0.9' numOctaves='2' stitchTiles='stitch'/></filter><rect width='100%' height='100%' filter='url(%23n)'/></svg>\")",
          backgroundPosition: `${gx}px ${gy}px`,
          mixBlendMode: "overlay",
        }}
      />
      <AbsoluteFill style={{ opacity: interpolate(frame, [0, 1], [1, 0], { extrapolateRight: "clamp" }), backgroundColor: "black" }} />
    </AbsoluteFill>
  );
};

/** White (or tinted) flash that fades out — put on a hard cut. */
export const Flash: React.FC<{ readonly color?: string; readonly len?: number }> = ({ color = "white", len = 8 }) => {
  const frame = useCurrentFrame();
  return (
    <AbsoluteFill
      style={{
        backgroundColor: color,
        mixBlendMode: "screen",
        opacity: interpolate(frame, [0, len], [0.85, 0], { extrapolateLeft: "clamp", extrapolateRight: "clamp" }),
      }}
    />
  );
};

/** Fade to/from black. */
export const Fade: React.FC<{ readonly from?: number; readonly to?: number }> = ({ from = 1, to = 0 }) => {
  const frame = useCurrentFrame();
  return <AbsoluteFill style={{ backgroundColor: "black", opacity: interpolate(frame, [0, 12], [from, to], { extrapolateLeft: "clamp", extrapolateRight: "clamp" }) }} />;
};
