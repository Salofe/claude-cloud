import { Audio } from "@remotion/media";
import { AbsoluteFill, Easing, interpolate, Sequence, staticFile, useCurrentFrame, useVideoConfig } from "remotion";
import { EndCard } from "./components/EndCard";
import { Flash, Grade } from "./components/Grade";
import { Shot } from "./components/Shot";
import { Line, Slam, SystemTag } from "./components/Type";
import { BODY, CYAN, GOLD, HEAD, RED, VIOLET } from "./theme";

const clamp = { extrapolateLeft: "clamp", extrapolateRight: "clamp" } as const;

/** Big centered title in the upper third (clear of TikTok's caption and button areas). */
const VTitle: React.FC<{ readonly kicker?: string; readonly text: string; readonly color?: string }> = ({ kicker, text, color = CYAN }) => {
  const frame = useCurrentFrame();
  const { durationInFrames } = useVideoConfig();
  return (
    <AbsoluteFill style={{ alignItems: "center", paddingTop: 300 }}>
      <AbsoluteFill style={{ background: "linear-gradient(180deg, rgba(2,4,12,.75) 0%, rgba(2,4,12,.35) 30%, rgba(2,4,12,0) 45%)" }} />
      <div style={{ position: "relative", textAlign: "center", padding: "0 70px", opacity: interpolate(frame, [durationInFrames - 6, durationInFrames], [1, 0], clamp) }}>
        {kicker ? (
          <div style={{ fontFamily: BODY, fontWeight: 700, fontSize: 44, letterSpacing: 6, color: GOLD, textTransform: "uppercase", textShadow: "0 2px 12px #000", opacity: interpolate(frame, [2, 9], [0, 1], clamp) }}>{kicker}</div>
        ) : null}
        <div
          style={{
            fontFamily: HEAD,
            fontWeight: 900,
            fontSize: 96,
            lineHeight: 1.05,
            color: "white",
            textShadow: `0 0 30px ${color}aa, 0 6px 26px #000`,
            scale: interpolate(frame, [0, 7], [1.4, 1], { ...clamp, easing: Easing.bezier(0.1, 0.9, 0.2, 1) }),
            filter: `blur(${interpolate(frame, [0, 6], [12, 0], clamp)}px)`,
          }}
        >
          {text}
        </div>
      </div>
    </AbsoluteFill>
  );
};

/** 30 s vertical cut for TikTok/Shorts: hook, the loop, the bosses, the galaxy, where to play. */
export const Vertical: React.FC = () => {
  const { fps } = useVideoConfig();
  const B = 60; // one bar
  return (
    <AbsoluteFill style={{ backgroundColor: "black" }}>
      {/* score: the drop (bars 22-32), the finale riser (35), the final hit and ring-out (36-38) */}
      <Audio src={staticFile("music.wav")} trimBefore={21 * B} durationInFrames={11 * B} />
      <Audio src={staticFile("music.wav")} from={11 * B} trimBefore={34 * B} durationInFrames={B} />
      <Audio
        src={staticFile("music.wav")}
        from={12 * B}
        trimBefore={35 * B}
        durationInFrames={3 * B}
        volume={(f) => interpolate(f, [3 * B - 40, 3 * B], [1, 0], clamp)}
      />

      <Sequence name="Hook rock" from={0} durationInFrames={B} premountFor={fps}>
        <Shot clip="mine-early" trim={100} zoom={[1.0, 1.12]} />
        <Line text="Empiezas minando una roca…" size={70} stagger={3} />
      </Sequence>
      <Sequence name="Hook black hole" from={B} durationInFrames={B} premountFor={fps}>
        <Shot clip="boss-sgra" trim={150} zoom={[1.0, 1.12]} />
        <Line text="…y terminas en un agujero negro" size={70} stagger={3} />
      </Sequence>
      <Sequence name="MINA" from={2 * B} durationInFrames={B} premountFor={fps}>
        <Shot clip="mine-rich" trim={30} />
        <Slam text="MINA" size={160} />
      </Sequence>
      <Sequence name="MEJORA" from={3 * B} durationInFrames={B} premountFor={fps}>
        <Shot clip="mine-saturn" trim={30} />
        <Slam text="MEJORA" size={140} color={GOLD} />
      </Sequence>
      <Sequence name="Explora" from={4 * B} durationInFrames={B} premountFor={fps}>
        <Shot clip="map-travel" trim={20} zoom={[1.15, 1.35]} />
        <VTitle kicker="Mapa estelar" text="EXPLORA" />
      </Sequence>
      <Sequence name="Pelea" from={5 * B} durationInFrames={B} premountFor={fps}>
        <Shot clip="pirates" trim={20} />
        <VTitle kicker="Piratas y guerras" text="PELEA" color={RED} />
      </Sequence>
      <Sequence name="Guardian" from={6 * B} durationInFrames={B} premountFor={fps}>
        <Shot clip="boss-sol" trim={30} />
        <VTitle kicker="Nube de Oort" text="JEFES ÉPICOS" color={RED} />
      </Sequence>
      <Sequence name="Jump" from={7 * B} durationInFrames={B} premountFor={fps}>
        <Shot clip="jump" trim={0} zoom={[1.0, 1.25]} />
        <Sequence durationInFrames={46}>
          <VTitle text="SALTA A OTRA ESTRELLA" color={VIOLET} />
        </Sequence>
      </Sequence>
      <Sequence name="Galaxy" from={8 * B} durationInFrames={B} premountFor={fps}>
        <Shot clip="galaxy" trim={0} zoom={[1.35, 1.15]} />
        <Slam text="15 SISTEMAS" size={104} />
      </Sequence>
      <Sequence name="Vega" from={9 * B} durationInFrames={30} premountFor={fps}>
        <Shot clip="boss-vega" trim={120} />
        <SystemTag n={7} name="VEGA" sub="El Leviatán" color={RED} pad="300px 0 0 70px" nameSize={96} />
      </Sequence>
      <Sequence name="Betelgeuse" from={9 * B + 30} durationInFrames={30} premountFor={fps}>
        <Shot clip="boss-betelgeuse" trim={0} />
        <SystemTag n={11} name="BETELGEUSE" sub="El Fénix" color={RED} pad="300px 0 0 70px" nameSize={96} />
      </Sequence>
      <Sequence name="Rigel" from={10 * B} durationInFrames={30} premountFor={fps}>
        <Shot clip="boss-rigel" trim={20} />
        <SystemTag n={10} name="RIGEL" sub="El Radiante" color={RED} pad="300px 0 0 70px" nameSize={96} />
      </Sequence>
      <Sequence name="Rim" from={10 * B + 30} durationInFrames={30} premountFor={fps}>
        <Shot clip="boss-rim" trim={0} />
        <SystemTag n={14} name="BORDE DEL NÚCLEO" sub="El Arconte" color={RED} pad="300px 0 0 70px" nameSize={72} />
      </Sequence>
      <Sequence name="Finale" from={11 * B} durationInFrames={B} premountFor={fps}>
        <Shot clip="boss-sgra" trim={0} zoom={[1.05, 1.3]} />
        <Line text="¿Llegarás al centro de la galaxia?" size={72} stagger={2} />
      </Sequence>
      <Sequence name="EndCard" from={12 * B} durationInFrames={3 * B} premountFor={fps}>
        <Shot clip="title-bg" trim={0} zoom={[1.3, 1.1]} dim={0.2} />
        <EndCard vertical url="play.clawcade.gg/g/LHgYcmEt" tagline="Mina · Mejora · Conquista la galaxia" cta="Juega gratis en tu navegador" platforms="PC y móvil · Sin descargas" />
      </Sequence>

      {[0, 2 * B, 8 * B, 10 * B, 12 * B].map((f) => (
        <Sequence key={f} from={f} durationInFrames={10}>
          <Flash />
        </Sequence>
      ))}
      {[B, 3 * B, 4 * B, 5 * B, 6 * B, 7 * B, 9 * B, 9 * B + 30, 10 * B + 30, 11 * B].map((f) => (
        <Sequence key={f} from={f} durationInFrames={6}>
          <Flash len={5} />
        </Sequence>
      ))}
      <Grade />
    </AbsoluteFill>
  );
};
