import { Video } from "@remotion/media";
import { AbsoluteFill, Easing, interpolate, staticFile, useCurrentFrame, useVideoConfig } from "remotion";

type Props = {
  readonly clip: string;
  /** source frames skipped before this shot starts */
  readonly trim?: number;
  /** slow camera push: start and end scale */
  readonly zoom?: [number, number];
  /** drift in px over the shot */
  readonly pan?: [number, number];
  readonly dim?: number;
  readonly blur?: number;
  readonly rate?: number;
};

/** A game clip with a slow cinematic push-in, a punchy zoom-out on the cut and a light grade. */
export const Shot: React.FC<Props> = ({ clip, trim = 0, zoom = [1.04, 1.12], pan = [0, 0], dim = 0, blur = 0, rate = 1 }) => {
  const frame = useCurrentFrame();
  const { durationInFrames, fps } = useVideoConfig();
  return (
    <AbsoluteFill style={{ backgroundColor: "#03050d", overflow: "hidden" }}>
      <Video
        src={staticFile(`clips/${clip}.mp4`)}
        trimBefore={trim}
        playbackRate={rate}
        muted
        objectFit="cover"
        premountFor={fps}
        style={{
          width: "100%",
          height: "100%",
          objectFit: "cover",
          filter: `saturate(1.15) contrast(1.06) brightness(${1 - dim})${blur ? ` blur(${blur}px)` : ""}`,
          scale: interpolate(frame, [0, 6, durationInFrames], [zoom[0] + 0.06, zoom[0], zoom[1]], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.bezier(0.2, 0.7, 0.3, 1),
          }),
          translate: interpolate(frame, [0, durationInFrames], [`0px 0px`, `${pan[0]}px ${pan[1]}px`], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          }),
        }}
      />
    </AbsoluteFill>
  );
};
